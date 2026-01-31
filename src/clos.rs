// TreeCL CLOS - Common Lisp Object System (TinyCLOS-style)
//
// Implements a minimal MOP-compliant object system.

use crate::symbol::{PackageId, SymbolId, SymbolTable};
use crate::types::NodeId;
use std::collections::HashMap;

/// Unique identifier for a class
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ClassId(pub u32);

/// Unique identifier for a generic function
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct GenericId(pub u32);

/// Unique identifier for a method
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct MethodId(pub u32);

/// A CLOS class definition
#[derive(Debug, Clone)]
pub struct Class {
    /// Class name
    pub name: SymbolId,
    /// Direct superclasses
    pub supers: Vec<ClassId>,
    /// Direct slots (slot-name -> slot-definition)
    pub slots: Vec<SlotDefinition>,
    /// Class precedence list (computed)
    pub cpl: Vec<ClassId>,
    /// Number of instance slots
    pub instance_size: usize,
}

/// A slot definition
#[derive(Debug, Clone)]
pub struct SlotDefinition {
    pub name: SymbolId,
    pub initform: Option<NodeId>,
    pub initarg: Option<SymbolId>,
    pub readers: Vec<SymbolId>,
    pub writers: Vec<SymbolId>,
    pub index: usize,
}

/// A generic function
#[derive(Debug, Clone)]
pub struct GenericFunction {
    pub name: SymbolId,
    pub lambda_list: Vec<SymbolId>,
    pub methods: Vec<MethodId>,
    pub method_combination: MethodCombination,
}

/// A method
#[derive(Debug, Clone)]
pub struct Method {
    /// Specializers (ClassIds for each parameter)
    pub specializers: Vec<ClassId>,
    /// Method qualifiers (:before, :after, :around, or primary)
    pub qualifiers: Vec<SymbolId>,
    /// Method body as a closure index or NodeId
    pub body: NodeId,
}

#[derive(Debug, Clone)]
pub enum MethodCombination {
    Standard,
    Operator {
        name: SymbolId,
        operator: SymbolId,
        identity_with_one_arg: bool,
    },
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum WrapperKind {
    Before,
    After,
}

/// An instance of a class
#[derive(Debug, Clone)]
pub struct Instance {
    pub class: ClassId,
    pub slots: Vec<NodeId>,
}

/// State for call-next-method
#[derive(Debug, Clone)]
pub struct NextMethodState {
    pub methods: Vec<MethodId>,
    pub args: Vec<NodeId>,
}

/// The CLOS metaobject protocol
pub struct MetaObjectProtocol {
    /// All classes
    classes: Vec<Class>,
    /// Class name -> ClassId lookup
    class_names: HashMap<SymbolId, ClassId>,
    /// Built-in class IDs
    pub t_class: ClassId,
    pub standard_object: ClassId,
    pub standard_class: ClassId,
    pub symbol_class: ClassId,
    pub integer_class: ClassId,
    /// All generic functions
    generics: Vec<GenericFunction>,
    /// Generic name -> GenericId
    generic_names: HashMap<SymbolId, GenericId>,
    /// All methods
    methods: Vec<Method>,
    /// Cached wrapper methods for standard method combination
    before_wrappers: HashMap<MethodId, MethodId>,
    after_wrappers: HashMap<MethodId, MethodId>,
    /// All instances
    instances: Vec<Instance>,
}

impl MetaObjectProtocol {
    pub fn get_instance_slots(&self, id: u32) -> Option<&[NodeId]> {
        self.instances.get(id as usize).map(|i| i.slots.as_slice())
    }

    pub fn get_method_body(&self, id: u32) -> Option<NodeId> {
        self.methods.get(id as usize).map(|m| m.body)
    }

    pub fn get_generic_methods(&self, id: u32) -> Option<&[MethodId]> {
        self.generics.get(id as usize).map(|g| g.methods.as_slice())
    }

    pub fn get_class_slots(&self, id: u32) -> Option<&[SlotDefinition]> {
        self.classes.get(id as usize).map(|c| c.slots.as_slice())
    }

    pub fn new(symbols: &mut SymbolTable) -> Self {
        let mut mop = Self {
            classes: Vec::new(),
            class_names: HashMap::new(),
            t_class: ClassId(0),
            standard_object: ClassId(1),
            standard_class: ClassId(2),
            symbol_class: ClassId(3),
            integer_class: ClassId(4),
            generics: Vec::new(),
            generic_names: HashMap::new(),
            methods: Vec::new(),
            before_wrappers: HashMap::new(),
            after_wrappers: HashMap::new(),
            instances: Vec::new(),
        };

        // Bootstrap the class hierarchy
        let cl = PackageId(1);

        // T class (root)
        let t_name = symbols.intern_in("T", cl);
        symbols.export_symbol(t_name);
        mop.classes.push(Class {
            name: t_name,
            supers: Vec::new(),
            slots: Vec::new(),
            cpl: vec![ClassId(0)],
            instance_size: 0,
        });
        mop.class_names.insert(t_name, ClassId(0));

        // STANDARD-OBJECT
        let so_name = symbols.intern_in("STANDARD-OBJECT", cl);
        symbols.export_symbol(so_name);
        mop.classes.push(Class {
            name: so_name,
            supers: vec![ClassId(0)],
            slots: Vec::new(),
            cpl: vec![ClassId(1), ClassId(0)],
            instance_size: 0,
        });
        mop.class_names.insert(so_name, ClassId(1));

        // STANDARD-CLASS
        let sc_name = symbols.intern_in("STANDARD-CLASS", cl);
        symbols.export_symbol(sc_name);
        mop.classes.push(Class {
            name: sc_name,
            supers: vec![ClassId(1)],
            slots: Vec::new(),
            cpl: vec![ClassId(2), ClassId(1), ClassId(0)],
            instance_size: 0,
        });
        mop.class_names.insert(sc_name, ClassId(2));

        // SYMBOL
        let sym_name = symbols.intern_in("SYMBOL", cl);
        symbols.export_symbol(sym_name);
        mop.classes.push(Class {
            name: sym_name,
            supers: vec![ClassId(0)],
            slots: Vec::new(),
            cpl: vec![ClassId(3), ClassId(0)],
            instance_size: 0,
        });
        mop.class_names.insert(sym_name, ClassId(3));

        // INTEGER
        let int_name = symbols.intern_in("INTEGER", cl);
        symbols.export_symbol(int_name);
        mop.classes.push(Class {
            name: int_name,
            supers: vec![ClassId(0)],
            slots: Vec::new(),
            cpl: vec![ClassId(4), ClassId(0)],
            instance_size: 0,
        });
        mop.class_names.insert(int_name, ClassId(4));

        mop
    }

    /// Define a new class
    pub fn define_class(
        &mut self,
        name: SymbolId,
        supers: Vec<ClassId>,
        slots: Vec<SlotDefinition>,
    ) -> ClassId {
        let id = if let Some(&existing_id) = self.class_names.get(&name) {
            existing_id
        } else {
            ClassId(self.classes.len() as u32)
        };

        let supers = if supers.is_empty() {
            vec![self.standard_object]
        } else {
            supers
        };

        // Compute CPL independent of mutation
        // Simplistic linearization: class + supers linearized
        let mut cpl = vec![id];
        // We need to resolve supers from self.classes which is immutable here? No we hold mutable self.
        // We can copy necessary data first.

        let mut super_cpls: Vec<Vec<ClassId>> = Vec::new();
        for &super_id in &supers {
            if let Some(super_class) = self.classes.get(super_id.0 as usize) {
                super_cpls.push(super_class.cpl.clone());
            }
        }

        for scpl in super_cpls {
            for c in scpl {
                if !cpl.contains(&c) {
                    cpl.push(c);
                }
            }
        }

        // Compute effective slots
        // Start with direct slots
        let mut effective_slots = Vec::new();

        // 1. Collect inherited slots from supers
        // Since supers already have effective slots (if this is sequential), we can use them.
        // Handling multiple inheritance duplicates: simplistically use first found.
        let mut seen_slots = std::collections::HashSet::new();

        // Traverse CPL (excluding self which is first) to gather slots in precedence order?
        // Actually, for instance layout, we want supers first usually (C++ style) or specific?
        // Let's just append super slots then direct slots.

        // Use supers directly?
        for &super_id in &supers {
            if let Some(super_class) = self.classes.get(super_id.0 as usize) {
                for slot in &super_class.slots {
                    if !seen_slots.contains(&slot.name) {
                        effective_slots.push(slot.clone());
                        seen_slots.insert(slot.name);
                    }
                }
            }
        }

        // 2. Add/Merge direct slots
        for direct_slot in slots {
            // Check if we shadow a slot
            if let Some(pos) = effective_slots
                .iter()
                .position(|s| s.name == direct_slot.name)
            {
                // Update existing slot (e.g. new initform) - Simplified: Overwrite
                // But we must keep the index? No, if we overwrite, we keep the position but update def.
                // Actually, if we re-layout, we can just replace.
                // But if we want to preserve layout of parent?
                // For now: Just overwrite at position.
                effective_slots[pos] = direct_slot;
            } else {
                effective_slots.push(direct_slot);
            }
        }

        // 3. Re-index
        for (i, slot) in effective_slots.iter_mut().enumerate() {
            slot.index = i;
        }

        let instance_size = effective_slots.len();

        // For now, let's just create/overwrite.
        let class_def = Class {
            name,
            supers,
            slots: effective_slots,
            cpl,
            instance_size,
        };

        if let Some(&existing_id) = self.class_names.get(&name) {
            self.classes[existing_id.0 as usize] = class_def;
            existing_id
        } else {
            self.classes.push(class_def);
            self.class_names.insert(name, id);
            id
        }
    }

    /// Find class by name
    pub fn find_class(&self, name: SymbolId) -> Option<ClassId> {
        self.class_names.get(&name).copied()
    }

    /// Get class by ID
    pub fn get_class(&self, id: ClassId) -> Option<&Class> {
        self.classes.get(id.0 as usize)
    }

    /// Create an instance of a class
    pub fn make_instance(&mut self, class_id: ClassId, nil_node: NodeId) -> Option<usize> {
        let class = self.classes.get(class_id.0 as usize)?;
        let slots = vec![nil_node; class.instance_size];

        let idx = self.instances.len();
        self.instances.push(Instance {
            class: class_id,
            slots,
        });

        Some(idx)
    }

    /// Get instance by index
    pub fn get_instance(&self, idx: usize) -> Option<&Instance> {
        self.instances.get(idx)
    }

    /// Get mutable instance by index
    pub fn get_instance_mut(&mut self, idx: usize) -> Option<&mut Instance> {
        self.instances.get_mut(idx)
    }

    /// Get slot value
    pub fn slot_value(&self, instance_idx: usize, slot_idx: usize) -> Option<NodeId> {
        let val = self
            .instances
            .get(instance_idx)
            .and_then(|inst| inst.slots.get(slot_idx).copied());
        eprintln!(
            "DEBUG: slot_value inst={} slot={} -> {:?}",
            instance_idx, slot_idx, val
        );
        val
    }

    /// Set slot value
    pub fn set_slot_value(&mut self, instance_idx: usize, slot_idx: usize, value: NodeId) {
        eprintln!(
            "DEBUG: set_slot_value inst={} slot={} val={:?}",
            instance_idx, slot_idx, value
        );
        if let Some(inst) = self.instances.get_mut(instance_idx) {
            if slot_idx < inst.slots.len() {
                inst.slots[slot_idx] = value;
            } else {
                eprintln!("DEBUG: set_slot_value OOB! len={}", inst.slots.len());
            }
        } else {
            eprintln!("DEBUG: set_slot_value Instance not found!");
        }
    }

    /// Define a generic function
    pub fn define_generic(&mut self, name: SymbolId, lambda_list: Vec<SymbolId>) -> GenericId {
        if let Some(&id) = self.generic_names.get(&name) {
            // Update existing generic (keep methods, update lambda list?)
            if let Some(gf) = self.generics.get_mut(id.0 as usize) {
                gf.lambda_list = lambda_list;
            }
            return id;
        }

        let id = GenericId(self.generics.len() as u32);

        self.generics.push(GenericFunction {
            name,
            lambda_list,
            methods: Vec::new(),
            method_combination: MethodCombination::Standard,
        });

        self.generic_names.insert(name, id);
        id
    }

    /// Find generic function by name
    pub fn find_generic(&self, name: SymbolId) -> Option<GenericId> {
        self.generic_names.get(&name).copied()
    }

    /// Get generic function by ID
    pub fn get_generic(&self, id: GenericId) -> Option<&GenericFunction> {
        self.generics.get(id.0 as usize)
    }

    pub fn set_generic_method_combination(
        &mut self,
        id: GenericId,
        method_combination: MethodCombination,
    ) {
        if let Some(gf) = self.generics.get_mut(id.0 as usize) {
            gf.method_combination = method_combination;
        }
    }

    /// Add a method to a generic function
    pub fn add_method(
        &mut self,
        generic_id: GenericId,
        specializers: Vec<ClassId>,
        qualifiers: Vec<SymbolId>,
        body: NodeId,
    ) -> MethodId {
        let method_id = MethodId(self.methods.len() as u32);

        self.methods.push(Method {
            specializers,
            qualifiers,
            body,
        });

        if let Some(gf) = self.generics.get_mut(generic_id.0 as usize) {
            gf.methods.push(method_id);
        }

        method_id
    }

    /// Add a method without attaching it to a generic function (used for wrappers).
    pub fn add_method_raw(
        &mut self,
        specializers: Vec<ClassId>,
        qualifiers: Vec<SymbolId>,
        body: NodeId,
    ) -> MethodId {
        let method_id = MethodId(self.methods.len() as u32);
        self.methods.push(Method {
            specializers,
            qualifiers,
            body,
        });
        method_id
    }

    /// Get method by ID
    pub fn get_method(&self, id: MethodId) -> Option<&Method> {
        self.methods.get(id.0 as usize)
    }

    pub fn get_wrapper(&self, kind: WrapperKind, id: MethodId) -> Option<MethodId> {
        match kind {
            WrapperKind::Before => self.before_wrappers.get(&id).copied(),
            WrapperKind::After => self.after_wrappers.get(&id).copied(),
        }
    }

    pub fn set_wrapper(&mut self, kind: WrapperKind, id: MethodId, wrapper: MethodId) {
        match kind {
            WrapperKind::Before => {
                self.before_wrappers.insert(id, wrapper);
            }
            WrapperKind::After => {
                self.after_wrappers.insert(id, wrapper);
            }
        }
    }

    /// Check if instance is of class (or subclass)
    pub fn instance_of(&self, instance_idx: usize, class_id: ClassId) -> bool {
        if let Some(inst) = self.instances.get(instance_idx) {
            if let Some(class) = self.classes.get(inst.class.0 as usize) {
                return class.cpl.contains(&class_id);
            }
        }
        false
    }

    /// Find applicable methods for given argument classes
    pub fn compute_applicable_methods(
        &self,
        generic_id: GenericId,
        arg_classes: &[ClassId],
    ) -> Vec<MethodId> {
        let gf = match self.get_generic(generic_id) {
            Some(gf) => gf,
            None => return Vec::new(),
        };

        let mut applicable = Vec::new();

        for &method_id in &gf.methods {
            if let Some(method) = self.get_method(method_id) {
                if self.method_applicable(method, arg_classes) {
                    applicable.push(method_id);
                }
            }
        }

        // Sort by specificity (most specific first)
        applicable.sort_by(|&a, &b| {
            let ma = self.get_method(a).unwrap();
            let mb = self.get_method(b).unwrap();
            self.compare_method_specificity(ma, mb, arg_classes)
        });

        applicable
    }

    pub fn method_applicable(&self, method: &Method, arg_classes: &[ClassId]) -> bool {
        if method.specializers.len() > arg_classes.len() {
            return false;
        }

        for (i, &spec) in method.specializers.iter().enumerate() {
            if let Some(&arg_class) = arg_classes.get(i) {
                if let Some(class) = self.classes.get(arg_class.0 as usize) {
                    if !class.cpl.contains(&spec) {
                        return false;
                    }
                } else {
                    return false;
                }
            }
        }

        true
    }

    fn compare_method_specificity(
        &self,
        ma: &Method,
        mb: &Method,
        arg_classes: &[ClassId],
    ) -> std::cmp::Ordering {
        // Compare based on argument class precedence lists (most specific first).
        for (i, arg_class) in arg_classes.iter().enumerate() {
            let cpl = match self.classes.get(arg_class.0 as usize) {
                Some(c) => &c.cpl,
                None => continue,
            };

            let sa = ma.specializers.get(i).copied().unwrap_or(self.t_class);
            let sb = mb.specializers.get(i).copied().unwrap_or(self.t_class);

            let posa = cpl.iter().position(|c| *c == sa).unwrap_or(usize::MAX);
            let posb = cpl.iter().position(|c| *c == sb).unwrap_or(usize::MAX);

            if posa != posb {
                return posa.cmp(&posb);
            }
        }

        std::cmp::Ordering::Equal
    }
    /// Get GC roots
    pub fn iter_roots(&self) -> Vec<NodeId> {
        let mut roots = Vec::new();
        // Trace Classes (initforms in slot definitions)
        for class in &self.classes {
            for slot in &class.slots {
                if let Some(initform) = slot.initform {
                    roots.push(initform);
                }
            }
        }

        // Trace Methods (bodies)
        for method in &self.methods {
            roots.push(method.body);
        }

        // Trace Instances (slot values) - REMOVED
        // Instances are not roots; they are reachable via handles in the graph.
        // If we marked them here, they would never be collected.

        roots
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::symbol::SymbolTable;

    #[test]
    fn test_bootstrap_classes() {
        let mut symbols = SymbolTable::new();
        let mop = MetaObjectProtocol::new(&mut symbols);

        assert_eq!(mop.t_class, ClassId(0));
        assert_eq!(mop.standard_object, ClassId(1));
        assert_eq!(mop.standard_class, ClassId(2));

        // T should be in all CPLs
        let so = mop.get_class(mop.standard_object).unwrap();
        assert!(so.cpl.contains(&mop.t_class));
    }

    #[test]
    fn test_define_class() {
        let mut symbols = SymbolTable::new();
        let mut mop = MetaObjectProtocol::new(&mut symbols);

        let point_name = symbols.intern("POINT");
        let x_name = symbols.intern("X");
        let y_name = symbols.intern("Y");

        let point_class = mop.define_class(
            point_name,
            vec![mop.standard_object],
            vec![
                SlotDefinition {
                    name: x_name,
                    initform: None,
                    initarg: None,
                    readers: Vec::new(),
                    writers: Vec::new(),
                    index: 0,
                },
                SlotDefinition {
                    name: y_name,
                    initform: None,
                    initarg: None,
                    readers: Vec::new(),
                    writers: Vec::new(),
                    index: 1,
                },
            ],
        );

        let class = mop.get_class(point_class).unwrap();
        assert_eq!(class.instance_size, 2);
        assert!(class.cpl.contains(&mop.t_class));
    }

    #[test]
    fn test_make_instance() {
        let mut symbols = SymbolTable::new();
        let mut mop = MetaObjectProtocol::new(&mut symbols);

        let point_name = symbols.intern("POINT");
        let x_name = symbols.intern("X");

        let point_class = mop.define_class(
            point_name,
            vec![mop.standard_object],
            vec![SlotDefinition {
                name: x_name,
                initform: None,
                initarg: None,
                readers: Vec::new(),
                writers: Vec::new(),
                index: 0,
            }],
        );

        let nil = NodeId(0);
        let inst_idx = mop.make_instance(point_class, nil).unwrap();

        let inst = mop.get_instance(inst_idx).unwrap();
        assert_eq!(inst.class, point_class);
        assert_eq!(inst.slots.len(), 1);
    }

    #[test]
    fn test_slot_access() {
        let mut symbols = SymbolTable::new();
        let mut mop = MetaObjectProtocol::new(&mut symbols);

        let point_name = symbols.intern("POINT");
        let x_name = symbols.intern("X");

        let point_class = mop.define_class(
            point_name,
            vec![mop.standard_object],
            vec![SlotDefinition {
                name: x_name,
                initform: None,
                initarg: None,
                readers: Vec::new(),
                writers: Vec::new(),
                index: 0,
            }],
        );

        let nil = NodeId(0);
        let val = NodeId(42);
        let inst_idx = mop.make_instance(point_class, nil).unwrap();

        // Set slot
        mop.set_slot_value(inst_idx, 0, val);

        // Get slot
        assert_eq!(mop.slot_value(inst_idx, 0), Some(val));
    }
}
