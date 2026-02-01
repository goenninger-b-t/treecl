fn parse_keywords_list(proc: &Process, args: &[NodeId]) -> HashMap<SymbolId, NodeId> {
    let mut keywords = HashMap::new();
    let mut i = 0;
    while i < args.len() {
        if i + 1 >= args.len() {
            break;
        }
        if let Some(key) = node_to_symbol(proc, args[i]) {
            keywords.insert(key, args[i + 1]);
        }
        i += 2;
    }
    keywords
}

fn list_to_vec(proc: &Process, list: NodeId) -> Vec<NodeId> {
    let mut vec = Vec::new();
    let mut curr = list;
    while let Node::Fork(head, tail) = proc.arena.inner.get_unchecked(curr).clone() {
        vec.push(head);
        curr = tail;
    }
    vec
}

fn parse_slot_def(
    proc: &Process,
    spec: NodeId,
    index: usize,
    ctx: &crate::context::GlobalContext,
) -> Result<crate::clos::SlotDefinition, crate::eval::ControlSignal> {
    use crate::clos::SlotDefinition;

    let (name_node, rest) = match proc.arena.inner.get_unchecked(spec) {
        Node::Leaf(OpaqueValue::Symbol(_)) => (spec, proc.make_nil()),
        Node::Fork(h, t) => (*h, *t),
        _ => {
            return Err(crate::eval::ControlSignal::Error(
                "Invalid slot spec".to_string(),
            ))
        }
    };

    let name = node_to_symbol(proc, name_node)
        .ok_or_else(|| crate::eval::ControlSignal::Error("Slot name must be symbol".to_string()))?;

    let rest_vec = list_to_vec(proc, rest);
    let props = parse_keywords_list(proc, &rest_vec);

    // Look up keyword symbols
    let syms = ctx.symbols.read().unwrap();
    let k_initform = syms.find("INITFORM").unwrap_or(SymbolId(0));
    let k_initfunction = syms.find("INITFUNCTION").unwrap_or(SymbolId(0));
    let k_initarg = syms.find("INITARG").unwrap_or(SymbolId(0));
    let k_reader = syms.find("READER").unwrap_or(SymbolId(0));
    let k_writer = syms.find("WRITER").unwrap_or(SymbolId(0));
    let k_accessor = syms.find("ACCESSOR").unwrap_or(SymbolId(0));
    let k_allocation = syms.find("ALLOCATION").unwrap_or(SymbolId(0));
    let k_type = syms.find("TYPE").unwrap_or(SymbolId(0));
    drop(syms);

    let initform = props.get(&k_initform).copied();
    let initfunction = props.get(&k_initfunction).copied();
    let initarg = props.get(&k_initarg).and_then(|&n| node_to_symbol(proc, n));

    let mut readers = Vec::new();
    let mut writers = Vec::new();

    if let Some(&r) = props.get(&k_reader) {
        if let Some(s) = node_to_symbol(proc, r) {
            readers.push(s);
        }
    }
    if let Some(&w) = props.get(&k_writer) {
        if let Some(s) = node_to_symbol(proc, w) {
            writers.push(s);
        }
    }
    if let Some(&a) = props.get(&k_accessor) {
        if let Some(s) = node_to_symbol(proc, a) {
            readers.push(s);
            writers.push(s); // TODO: strict setf name?
        }
    }

    let allocation = if let Some(&alloc_node) = props.get(&k_allocation) {
        if let Some(sym) = node_to_symbol(proc, alloc_node) {
            let name = ctx
                .symbols
                .read()
                .unwrap()
                .symbol_name(sym)
                .unwrap_or("")
                .to_string();
            if name == "CLASS" {
                crate::clos::SlotAllocation::Class
            } else {
                crate::clos::SlotAllocation::Instance
            }
        } else {
            crate::clos::SlotAllocation::Instance
        }
    } else {
        crate::clos::SlotAllocation::Instance
    };

    let slot_type = props.get(&k_type).copied();

    Ok(SlotDefinition {
        name,
        initform,
        initfunction,
        initarg,
        readers,
        writers,
        allocation,
        slot_type,
        class_value: None,
        index,
    })
}

fn prim_ensure_class(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    use crate::clos::{ClassId, SlotDefinition};

    if args.is_empty() {
        return Err(crate::eval::ControlSignal::Error(
            "ENSURE-CLASS requires at least a name".to_string(),
        ));
    }

    let name_node = args[0];
    let name = node_to_symbol(proc, name_node).ok_or_else(|| {
        crate::eval::ControlSignal::Error("Class name must be a symbol".to_string())
    })?;

    let kwargs = parse_keywords_list(proc, &args[1..]);

    let syms = ctx.symbols.read().unwrap();
    let kw_supers = syms.find("DIRECT-SUPERCLASSES").unwrap_or(SymbolId(0));
    let kw_slots = syms.find("DIRECT-SLOTS").unwrap_or(SymbolId(0));
    drop(syms);

    let mut supers = Vec::new();
    if let Some(&supers_node) = kwargs.get(&kw_supers) {
        for head in list_to_vec(proc, supers_node) {
            let class_id = match proc.arena.inner.get_unchecked(head) {
                Node::Leaf(OpaqueValue::Class(id)) => Some(ClassId(*id)),
                Node::Leaf(OpaqueValue::Symbol(id)) => proc.mop.find_class(SymbolId(*id)),
                _ => None,
            };

            // If symbol and not found, error? Or forward reference?
            // For now error.
            if let Some(cid) = class_id {
                supers.push(cid);
            } else {
                return Err(crate::eval::ControlSignal::Error(format!(
                    "Unknown superclass: {:?}",
                    head
                )));
            }
        }
    }

    let mut slots = Vec::new();
    if let Some(&slots_node) = kwargs.get(&kw_slots) {
        let mut index = 0;
        for head in list_to_vec(proc, slots_node) {
            let slot_def = parse_slot_def(proc, head, index, ctx)?;
            slots.push(slot_def);
            index += 1;
        }
    }

    let class_id = proc.mop.define_class(name, supers, slots);
    Ok(proc
        .arena
        .inner
        .alloc(Node::Leaf(OpaqueValue::Class(class_id.0))))
}

fn prim_ensure_generic_function(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    use crate::clos::GenericId;

    if args.is_empty() {
        return Err(crate::eval::ControlSignal::Error(
            "ENSURE-GENERIC requires name".to_string(),
        ));
    }
    let name_node = args[0];
    let name = node_to_symbol(proc, name_node).ok_or(crate::eval::ControlSignal::Error(
        "Generic name != symbol".to_string(),
    ))?;

    let kwargs = parse_keywords_list(proc, &args[1..]);

    let syms = ctx.symbols.read().unwrap();
    let kw_lambda_list = syms.find("LAMBDA-LIST").unwrap_or(SymbolId(0));
    drop(syms);

    let mut lambda_list = Vec::new();
    if let Some(&ll_node) = kwargs.get(&kw_lambda_list) {
        for head in list_to_vec(proc, ll_node) {
            if let Some(s) = node_to_symbol(proc, head) {
                lambda_list.push(s);
            }
        }
    }

    let gid = proc.mop.define_generic(name, lambda_list);
    Ok(proc
        .arena
        .inner
        .alloc(Node::Leaf(OpaqueValue::Generic(gid.0))))
}

fn prim_ensure_method(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    use crate::clos::{ClassId, GenericId};

    if args.is_empty() {
        return Err(crate::eval::ControlSignal::Error(
            "ENSURE-METHOD requires GF".to_string(),
        ));
    }

    let gf_node = args[0];
    let gf_id = match proc.arena.inner.get_unchecked(gf_node) {
        Node::Leaf(OpaqueValue::Generic(id)) => GenericId(*id),
        Node::Leaf(OpaqueValue::Symbol(id)) => {
            // Auto-vivify generic function if it doesn't exist?
            // Usually defmethod does this.
            let name = SymbolId(*id);
            if let Some(gid) = proc.mop.find_generic(name) {
                gid
            } else {
                // Determine lambda list from specializers/args?
                // For now, empty or catch-all?
                // Let's require it to exist or create with empty LL.
                proc.mop.define_generic(name, Vec::new())
            }
        }
        _ => {
            return Err(crate::eval::ControlSignal::Error(
                "Invalid GF spec".to_string(),
            ))
        }
    };

    let kwargs = parse_keywords_list(proc, &args[1..]);

    let syms = ctx.symbols.read().unwrap();
    let kw_specializers = syms.find("SPECIALIZERS").unwrap_or(SymbolId(0));
    let kw_qualifiers = syms.find("QUALIFIERS").unwrap_or(SymbolId(0));
    let kw_body = syms.find("BODY").unwrap_or(SymbolId(0));
    let kw_lambda_list = syms.find("LAMBDA-LIST").unwrap_or(SymbolId(0));
    drop(syms);

    let mut specializers = Vec::new();
    if let Some(&specs_node) = kwargs.get(&kw_specializers) {
        for head in list_to_vec(proc, specs_node) {
            let class_id = match proc.arena.inner.get_unchecked(head) {
                Node::Leaf(OpaqueValue::Class(id)) => Some(ClassId(*id)),
                Node::Leaf(OpaqueValue::Symbol(id)) => proc.mop.find_class(SymbolId(*id)),
                _ => None, // T or specific logic?
            };
            // If not found, default to T? Or error.
            if let Some(cid) = class_id {
                specializers.push(cid);
            } else {
                specializers.push(proc.mop.t_class);
            }
        }
    }

    let mut qualifiers = Vec::new();
    if let Some(&q_node) = kwargs.get(&kw_qualifiers) {
        for head in list_to_vec(proc, q_node) {
            if let Some(s) = node_to_symbol(proc, head) {
                qualifiers.push(s);
            }
        }
    }

    let body = *kwargs.get(&kw_body).unwrap_or(&proc.make_nil());

    let mut lambda_list = Vec::new();
    if let Some(&ll_node) = kwargs.get(&kw_lambda_list) {
        for head in list_to_vec(proc, ll_node) {
            if let Some(sym) = node_to_symbol(proc, head) {
                lambda_list.push(sym);
            }
        }
    }

    let mid = proc
        .mop
        .add_method(gf_id, specializers, qualifiers, lambda_list, body);

    // Return method object?
    Ok(proc.make_nil()) // TODO: Return Method object appropriately
}
