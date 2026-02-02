// TreeCL CLOS - Common Lisp Object System (TinyCLOS-style)
//
// Implements a minimal MOP-compliant object system.

use crate::arena::{Arena, Node};
use crate::symbol::{PackageId, SymbolId, SymbolTable};
use crate::types::{NodeId, OpaqueValue};
use num_traits::ToPrimitive;
use std::collections::HashMap;

/// Unique identifier for a class
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ClassId(pub u32);

pub const STANDALONE_SLOT_DEF_CLASS_ID: u32 = u32::MAX;

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
    /// Metaclass (class of this class)
    pub metaclass: ClassId,
    /// Direct superclasses
    pub supers: Vec<ClassId>,
    /// Direct slot definitions
    pub direct_slots: Vec<SlotDefinition>,
    /// Direct slots (slot-name -> slot-definition)
    pub slots: Vec<SlotDefinition>,
    /// Class precedence list (computed)
    pub cpl: Vec<ClassId>,
    /// Number of instance slots
    pub instance_size: usize,
    /// Direct subclasses
    pub direct_subclasses: Vec<ClassId>,
    /// Whether class is finalized
    pub finalized: bool,
    /// Direct default initargs (as keyword/value pairs)
    pub direct_default_initargs: Vec<(SymbolId, NodeId)>,
    /// Effective default initargs (computed)
    pub default_initargs: Vec<(SymbolId, NodeId)>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SlotAllocation {
    Instance,
    Class,
}

/// A slot definition
#[derive(Debug, Clone)]
pub struct SlotDefinition {
    pub name: SymbolId,
    pub initform: Option<NodeId>,
    pub initfunction: Option<NodeId>,
    pub initarg: Option<SymbolId>,
    pub readers: Vec<SymbolId>,
    pub writers: Vec<SymbolId>,
    pub allocation: SlotAllocation,
    pub slot_type: Option<NodeId>,
    pub class_value: Option<NodeId>,
    pub index: usize,
}

/// A generic function
#[derive(Debug, Clone)]
pub struct GenericFunction {
    pub name: SymbolId,
    pub lambda_list: Vec<SymbolId>,
    pub required_parameters: Vec<SymbolId>,
    pub argument_precedence_order: Option<Vec<SymbolId>>,
    pub discriminating_function: Option<NodeId>,
    pub method_cache: HashMap<Vec<ClassId>, NodeId>,
    pub methods: Vec<MethodId>,
    pub method_combination: MethodCombination,
}

/// A method
#[derive(Debug, Clone)]
pub struct Method {
    /// Specializers (ClassIds or EQL specializers for each parameter)
    pub specializers: Vec<Specializer>,
    /// Method qualifiers (:before, :after, :around, or primary)
    pub qualifiers: Vec<SymbolId>,
    /// Method lambda list (symbols)
    pub lambda_list: Vec<SymbolId>,
    /// Method body as a closure index or NodeId
    pub body: NodeId,
    /// Generic function this method is attached to
    pub generic: Option<GenericId>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Specializer {
    Class(ClassId),
    Eql(u32),
}

#[derive(Debug, Clone)]
pub struct EqlSpecializer {
    pub object: NodeId,
}

#[derive(Debug, Clone)]
pub enum MethodCombination {
    Standard,
    Operator {
        name: SymbolId,
        operator: SymbolId,
        identity_with_one_arg: bool,
    },
    UserLong {
        name: SymbolId,
        expander: NodeId,
        options: NodeId,
    },
}

#[derive(Debug, Clone)]
pub enum MethodCombinationDef {
    Operator {
        operator: SymbolId,
        identity_with_one_arg: bool,
    },
    Long {
        expander: NodeId,
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
    /// ClassId -> metaobject instance index
    class_meta_instances: HashMap<ClassId, usize>,
    /// Built-in class IDs
    pub t_class: ClassId,
    pub standard_object: ClassId,
    pub standard_class: ClassId,
    pub standard_generic_function: ClassId,
    pub standard_method: ClassId,
    pub standard_direct_slot_definition: ClassId,
    pub standard_effective_slot_definition: ClassId,
    pub eql_specializer_class: ClassId,
    pub symbol_class: ClassId,
    pub integer_class: ClassId,
    /// All generic functions
    generics: Vec<GenericFunction>,
    /// Generic name -> GenericId
    generic_names: HashMap<SymbolId, GenericId>,
    /// All methods
    methods: Vec<Method>,
    /// GenericId -> metaobject instance index
    generic_meta_instances: HashMap<GenericId, usize>,
    /// MethodId -> metaobject instance index
    method_meta_instances: HashMap<MethodId, usize>,
    /// Slot-definition key -> metaobject instance index
    slot_def_meta_instances: HashMap<(ClassId, u32, bool), usize>,
    /// Standalone slot definitions (not attached to a class)
    standalone_slot_defs: Vec<SlotDefinition>,
    /// Cached wrapper methods for standard method combination
    before_wrappers: HashMap<MethodId, MethodId>,
    after_wrappers: HashMap<MethodId, MethodId>,
    /// Registered method combinations
    method_combinations: HashMap<SymbolId, MethodCombinationDef>,
    /// All instances
    instances: Vec<Instance>,
    /// Interned EQL specializers
    eql_specializers: Vec<EqlSpecializer>,
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
            class_meta_instances: HashMap::new(),
            t_class: ClassId(0),
            standard_object: ClassId(1),
            standard_class: ClassId(2),
            standard_generic_function: ClassId(0),
            standard_method: ClassId(0),
            standard_direct_slot_definition: ClassId(0),
            standard_effective_slot_definition: ClassId(0),
            eql_specializer_class: ClassId(0),
            symbol_class: ClassId(3),
            integer_class: ClassId(4),
            generics: Vec::new(),
            generic_names: HashMap::new(),
            methods: Vec::new(),
            generic_meta_instances: HashMap::new(),
            method_meta_instances: HashMap::new(),
            slot_def_meta_instances: HashMap::new(),
            standalone_slot_defs: Vec::new(),
            before_wrappers: HashMap::new(),
            after_wrappers: HashMap::new(),
            method_combinations: HashMap::new(),
            instances: Vec::new(),
            eql_specializers: Vec::new(),
        };

        // Bootstrap the class hierarchy
        let cl = PackageId(1);

        // T class (root)
        let t_name = symbols.intern_in("T", cl);
        symbols.export_symbol(t_name);
        mop.classes.push(Class {
            name: t_name,
            metaclass: ClassId(2),
            supers: Vec::new(),
            direct_slots: Vec::new(),
            slots: Vec::new(),
            cpl: vec![ClassId(0)],
            instance_size: 0,
            direct_subclasses: Vec::new(),
            finalized: true,
            direct_default_initargs: Vec::new(),
            default_initargs: Vec::new(),
        });
        mop.class_names.insert(t_name, ClassId(0));

        // STANDARD-OBJECT
        let so_name = symbols.intern_in("STANDARD-OBJECT", cl);
        symbols.export_symbol(so_name);
        mop.classes.push(Class {
            name: so_name,
            metaclass: ClassId(2),
            supers: vec![ClassId(0)],
            direct_slots: Vec::new(),
            slots: Vec::new(),
            cpl: vec![ClassId(1), ClassId(0)],
            instance_size: 0,
            direct_subclasses: Vec::new(),
            finalized: true,
            direct_default_initargs: Vec::new(),
            default_initargs: Vec::new(),
        });
        mop.class_names.insert(so_name, ClassId(1));

        // STANDARD-CLASS
        let sc_name = symbols.intern_in("STANDARD-CLASS", cl);
        symbols.export_symbol(sc_name);
        mop.classes.push(Class {
            name: sc_name,
            metaclass: ClassId(2),
            supers: vec![ClassId(1)],
            direct_slots: Vec::new(),
            slots: Vec::new(),
            cpl: vec![ClassId(2), ClassId(1), ClassId(0)],
            instance_size: 0,
            direct_subclasses: Vec::new(),
            finalized: true,
            direct_default_initargs: Vec::new(),
            default_initargs: Vec::new(),
        });
        mop.class_names.insert(sc_name, ClassId(2));

        // SYMBOL
        let sym_name = symbols.intern_in("SYMBOL", cl);
        symbols.export_symbol(sym_name);
        mop.classes.push(Class {
            name: sym_name,
            metaclass: ClassId(2),
            supers: vec![ClassId(0)],
            direct_slots: Vec::new(),
            slots: Vec::new(),
            cpl: vec![ClassId(3), ClassId(0)],
            instance_size: 0,
            direct_subclasses: Vec::new(),
            finalized: true,
            direct_default_initargs: Vec::new(),
            default_initargs: Vec::new(),
        });
        mop.class_names.insert(sym_name, ClassId(3));

        // INTEGER
        let int_name = symbols.intern_in("INTEGER", cl);
        symbols.export_symbol(int_name);
        mop.classes.push(Class {
            name: int_name,
            metaclass: ClassId(2),
            supers: vec![ClassId(0)],
            direct_slots: Vec::new(),
            slots: Vec::new(),
            cpl: vec![ClassId(4), ClassId(0)],
            instance_size: 0,
            direct_subclasses: Vec::new(),
            finalized: true,
            direct_default_initargs: Vec::new(),
            default_initargs: Vec::new(),
        });
        mop.class_names.insert(int_name, ClassId(4));

        // EQL-SPECIALIZER
        let eql_spec_name = symbols.intern_in("EQL-SPECIALIZER", cl);
        symbols.export_symbol(eql_spec_name);
        let eql_spec_id = ClassId(mop.classes.len() as u32);
        mop.classes.push(Class {
            name: eql_spec_name,
            metaclass: ClassId(2),
            supers: vec![mop.standard_object],
            direct_slots: Vec::new(),
            slots: Vec::new(),
            cpl: vec![eql_spec_id, mop.standard_object, mop.t_class],
            instance_size: 0,
            direct_subclasses: Vec::new(),
            finalized: true,
            direct_default_initargs: Vec::new(),
            default_initargs: Vec::new(),
        });
        mop.class_names.insert(eql_spec_name, eql_spec_id);
        mop.eql_specializer_class = eql_spec_id;

        // Populate direct subclasses for bootstrap classes.
        let class_count = mop.classes.len();
        for id in 0..class_count {
            let supers = mop.classes[id].supers.clone();
            for super_id in supers {
                if let Some(cls) = mop.classes.get_mut(super_id.0 as usize) {
                    let cid = ClassId(id as u32);
                    if !cls.direct_subclasses.contains(&cid) {
                        cls.direct_subclasses.push(cid);
                    }
                }
            }
        }

        // Define standard-class slots for class metaobjects.
        let kw = PackageId(0);
        let k_name = symbols.intern_in("NAME", cl);
        let k_direct_supers = symbols.intern_in("DIRECT-SUPERCLASSES", cl);
        let k_direct_subs = symbols.intern_in("DIRECT-SUBCLASSES", cl);
        let k_direct_slots = symbols.intern_in("DIRECT-SLOTS", cl);
        let k_cpl = symbols.intern_in("CLASS-PRECEDENCE-LIST", cl);
        let k_slots = symbols.intern_in("SLOTS", cl);
        let k_finalized = symbols.intern_in("FINALIZED-P", cl);
        let k_instance_size = symbols.intern_in("INSTANCE-SIZE", cl);
        let k_direct_default_initargs = symbols.intern_in("DIRECT-DEFAULT-INITARGS", cl);
        let k_default_initargs = symbols.intern_in("DEFAULT-INITARGS", cl);
        // Export metaobject slot names so CL-USER inherits them.
        for sym in [
            k_name,
            k_direct_supers,
            k_direct_subs,
            k_direct_slots,
            k_cpl,
            k_slots,
            k_finalized,
            k_instance_size,
            k_direct_default_initargs,
            k_default_initargs,
        ] {
            symbols.export_symbol(sym);
        }

        let kw_name = symbols.intern_in("NAME", kw);
        let kw_direct_supers = symbols.intern_in("DIRECT-SUPERCLASSES", kw);
        let kw_direct_subs = symbols.intern_in("DIRECT-SUBCLASSES", kw);
        let kw_direct_slots = symbols.intern_in("DIRECT-SLOTS", kw);
        let kw_cpl = symbols.intern_in("CLASS-PRECEDENCE-LIST", kw);
        let kw_slots = symbols.intern_in("SLOTS", kw);
        let kw_finalized = symbols.intern_in("FINALIZED-P", kw);
        let kw_instance_size = symbols.intern_in("INSTANCE-SIZE", kw);
        let kw_direct_default_initargs = symbols.intern_in("DIRECT-DEFAULT-INITARGS", kw);
        let kw_default_initargs = symbols.intern_in("DEFAULT-INITARGS", kw);

        let mut sc_slots = Vec::new();
        let mut push_slot = |name: SymbolId, initarg: SymbolId, index: usize| {
            sc_slots.push(SlotDefinition {
                name,
                initform: None,
                initfunction: None,
                initarg: Some(initarg),
                readers: Vec::new(),
                writers: Vec::new(),
                allocation: SlotAllocation::Instance,
                slot_type: None,
                class_value: None,
                index,
            });
        };
        push_slot(k_name, kw_name, 0);
        push_slot(k_direct_supers, kw_direct_supers, 1);
        push_slot(k_direct_subs, kw_direct_subs, 2);
        push_slot(k_direct_slots, kw_direct_slots, 3);
        push_slot(k_cpl, kw_cpl, 4);
        push_slot(k_slots, kw_slots, 5);
        push_slot(k_finalized, kw_finalized, 6);
        push_slot(k_instance_size, kw_instance_size, 7);
        push_slot(k_direct_default_initargs, kw_direct_default_initargs, 8);
        push_slot(k_default_initargs, kw_default_initargs, 9);

        let _ = mop.define_class(sc_name, vec![mop.standard_object], sc_slots);

        // STANDARD-GENERIC-FUNCTION
        let sgf_name = symbols.intern_in("STANDARD-GENERIC-FUNCTION", cl);
        symbols.export_symbol(sgf_name);
        let k_lambda_list = symbols.intern_in("LAMBDA-LIST", cl);
        let k_methods = symbols.intern_in("METHODS", cl);
        let k_method_combination = symbols.intern_in("METHOD-COMBINATION", cl);
        let k_arg_precedence = symbols.intern_in("ARGUMENT-PRECEDENCE-ORDER", cl);
        for sym in [k_lambda_list, k_methods, k_method_combination, k_arg_precedence] {
            symbols.export_symbol(sym);
        }
        let kw_lambda_list = symbols.intern_in("LAMBDA-LIST", kw);
        let kw_methods = symbols.intern_in("METHODS", kw);
        let kw_method_combination = symbols.intern_in("METHOD-COMBINATION", kw);
        let kw_arg_precedence = symbols.intern_in("ARGUMENT-PRECEDENCE-ORDER", kw);

        let mut sgf_slots = Vec::new();
        let mut push_sgf_slot = |name: SymbolId, initarg: SymbolId, index: usize| {
            sgf_slots.push(SlotDefinition {
                name,
                initform: None,
                initfunction: None,
                initarg: Some(initarg),
                readers: Vec::new(),
                writers: Vec::new(),
                allocation: SlotAllocation::Instance,
                slot_type: None,
                class_value: None,
                index,
            });
        };
        push_sgf_slot(k_name, kw_name, 0);
        push_sgf_slot(k_lambda_list, kw_lambda_list, 1);
        push_sgf_slot(k_methods, kw_methods, 2);
        push_sgf_slot(k_method_combination, kw_method_combination, 3);
        push_sgf_slot(k_arg_precedence, kw_arg_precedence, 4);
        let sgf_id = mop.define_class(sgf_name, vec![mop.standard_object], sgf_slots);
        mop.standard_generic_function = sgf_id;

        // STANDARD-METHOD
        let sm_name = symbols.intern_in("STANDARD-METHOD", cl);
        symbols.export_symbol(sm_name);
        let k_qualifiers = symbols.intern_in("QUALIFIERS", cl);
        let k_specializers = symbols.intern_in("SPECIALIZERS", cl);
        let k_generic_function = symbols.intern_in("GENERIC-FUNCTION", cl);
        let k_function = symbols.intern_in("FUNCTION", cl);
        for sym in [
            k_qualifiers,
            k_specializers,
            k_generic_function,
            k_function,
        ] {
            symbols.export_symbol(sym);
        }
        let kw_qualifiers = symbols.intern_in("QUALIFIERS", kw);
        let kw_specializers = symbols.intern_in("SPECIALIZERS", kw);
        let kw_generic_function = symbols.intern_in("GENERIC-FUNCTION", kw);
        let kw_function = symbols.intern_in("FUNCTION", kw);

        let mut sm_slots = Vec::new();
        let mut push_sm_slot = |name: SymbolId, initarg: SymbolId, index: usize| {
            sm_slots.push(SlotDefinition {
                name,
                initform: None,
                initfunction: None,
                initarg: Some(initarg),
                readers: Vec::new(),
                writers: Vec::new(),
                allocation: SlotAllocation::Instance,
                slot_type: None,
                class_value: None,
                index,
            });
        };
        push_sm_slot(k_lambda_list, kw_lambda_list, 0);
        push_sm_slot(k_qualifiers, kw_qualifiers, 1);
        push_sm_slot(k_specializers, kw_specializers, 2);
        push_sm_slot(k_generic_function, kw_generic_function, 3);
        push_sm_slot(k_function, kw_function, 4);
        let sm_id = mop.define_class(sm_name, vec![mop.standard_object], sm_slots);
        mop.standard_method = sm_id;

        // STANDARD-DIRECT-SLOT-DEFINITION / STANDARD-EFFECTIVE-SLOT-DEFINITION
        let sdsd_name = symbols.intern_in("STANDARD-DIRECT-SLOT-DEFINITION", cl);
        let sesd_name = symbols.intern_in("STANDARD-EFFECTIVE-SLOT-DEFINITION", cl);
        symbols.export_symbol(sdsd_name);
        symbols.export_symbol(sesd_name);
        let k_initform = symbols.intern_in("INITFORM", cl);
        let k_initfunction = symbols.intern_in("INITFUNCTION", cl);
        let k_initargs = symbols.intern_in("INITARGS", cl);
        let k_readers = symbols.intern_in("READERS", cl);
        let k_writers = symbols.intern_in("WRITERS", cl);
        let k_allocation = symbols.intern_in("ALLOCATION", cl);
        let k_type = symbols.intern_in("TYPE", cl);
        let k_location = symbols.intern_in("LOCATION", cl);
        for sym in [
            k_initform,
            k_initfunction,
            k_initargs,
            k_readers,
            k_writers,
            k_allocation,
            k_type,
            k_location,
        ] {
            symbols.export_symbol(sym);
        }
        let kw_initform = symbols.intern_in("INITFORM", kw);
        let kw_initfunction = symbols.intern_in("INITFUNCTION", kw);
        let kw_initargs = symbols.intern_in("INITARGS", kw);
        let kw_readers = symbols.intern_in("READERS", kw);
        let kw_writers = symbols.intern_in("WRITERS", kw);
        let kw_allocation = symbols.intern_in("ALLOCATION", kw);
        let kw_type = symbols.intern_in("TYPE", kw);
        let kw_location = symbols.intern_in("LOCATION", kw);

        let mut slotdef_slots = Vec::new();
        let mut push_slotdef_slot = |name: SymbolId, initarg: SymbolId, index: usize| {
            slotdef_slots.push(SlotDefinition {
                name,
                initform: None,
                initfunction: None,
                initarg: Some(initarg),
                readers: Vec::new(),
                writers: Vec::new(),
                allocation: SlotAllocation::Instance,
                slot_type: None,
                class_value: None,
                index,
            });
        };
        push_slotdef_slot(k_name, kw_name, 0);
        push_slotdef_slot(k_initform, kw_initform, 1);
        push_slotdef_slot(k_initfunction, kw_initfunction, 2);
        push_slotdef_slot(k_initargs, kw_initargs, 3);
        push_slotdef_slot(k_readers, kw_readers, 4);
        push_slotdef_slot(k_writers, kw_writers, 5);
        push_slotdef_slot(k_allocation, kw_allocation, 6);
        push_slotdef_slot(k_type, kw_type, 7);
        push_slotdef_slot(k_location, kw_location, 8);

        let sdsd_id = mop.define_class(sdsd_name, vec![mop.standard_object], slotdef_slots.clone());
        let sesd_id = mop.define_class(sesd_name, vec![mop.standard_object], slotdef_slots);
        mop.standard_direct_slot_definition = sdsd_id;
        mop.standard_effective_slot_definition = sesd_id;

        mop
    }

    /// Define a new class with optional metaclass and direct default initargs.
    pub fn define_class_with_meta(
        &mut self,
        name: SymbolId,
        supers: Vec<ClassId>,
        slots: Vec<SlotDefinition>,
        metaclass: Option<ClassId>,
        direct_default_initargs: Vec<(SymbolId, NodeId)>,
    ) -> ClassId {
        let existing_id = self.class_names.get(&name).copied();
        let id = existing_id.unwrap_or_else(|| ClassId(self.classes.len() as u32));

        let supers = if supers.is_empty() {
            vec![self.standard_object]
        } else {
            supers
        };
        let supers_clone = supers.clone();
        let metaclass = metaclass
            .or_else(|| {
                existing_id.and_then(|eid| {
                    self.classes
                        .get(eid.0 as usize)
                        .map(|c| c.metaclass)
                })
            })
            .unwrap_or(self.standard_class);

        // Track old supers for subclass list maintenance.
        let old_supers = existing_id
            .and_then(|eid| self.classes.get(eid.0 as usize).map(|c| c.supers.clone()))
            .unwrap_or_default();

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
        let mut effective_slots: Vec<SlotDefinition> = Vec::new();

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
                        let mut inherited = slot.clone();
                        if inherited.allocation == SlotAllocation::Class {
                            inherited.class_value = None;
                        }
                        effective_slots.push(inherited);
                        seen_slots.insert(slot.name);
                    }
                }
            }
        }

        // 2. Add/Merge direct slots
        for direct_slot in slots.clone() {
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
        let mut instance_index = 0;
        for slot in effective_slots.iter_mut() {
            if slot.allocation == SlotAllocation::Instance {
                slot.index = instance_index;
                instance_index += 1;
            } else {
                slot.index = usize::MAX;
            }
            if slot.allocation == SlotAllocation::Class && slot.class_value.is_none() {
                slot.class_value = slot.initform;
            }
        }

        let instance_size = instance_index;

        // Compute effective default initargs from CPL (general -> specific).
        let mut default_initargs: Vec<(SymbolId, NodeId)> = Vec::new();
        let mut initarg_positions: HashMap<SymbolId, usize> = HashMap::new();
        for &cid in cpl.iter().rev() {
            let pairs = if cid == id {
                direct_default_initargs.clone()
            } else {
                self.classes
                    .get(cid.0 as usize)
                    .map(|c| c.direct_default_initargs.clone())
                    .unwrap_or_default()
            };
            for (key, val) in pairs {
                if let Some(pos) = initarg_positions.get(&key) {
                    default_initargs[*pos].1 = val;
                } else {
                    initarg_positions.insert(key, default_initargs.len());
                    default_initargs.push((key, val));
                }
            }
        }

        // For now, let's just create/overwrite.
        let class_def = Class {
            name,
            metaclass,
            supers: supers.clone(),
            direct_slots: slots,
            slots: effective_slots,
            cpl,
            instance_size,
            direct_subclasses: Vec::new(),
            finalized: true,
            direct_default_initargs,
            default_initargs,
        };

        if let Some(existing_id) = existing_id {
            // Preserve existing direct subclasses list when redefining.
            let direct_subclasses = self.classes[existing_id.0 as usize]
                .direct_subclasses
                .clone();
            let mut class_def = class_def;
            class_def.direct_subclasses = direct_subclasses;
            self.classes[existing_id.0 as usize] = class_def;
        } else {
            self.classes.push(class_def);
            self.class_names.insert(name, id);
        }

        // Update direct subclass links on supers.
        // Remove from old supers no longer referenced.
        for old_super in old_supers.iter() {
            if !supers.contains(old_super) {
                if let Some(cls) = self.classes.get_mut(old_super.0 as usize) {
                    cls.direct_subclasses.retain(|c| *c != id);
                }
            }
        }
        // Add to new supers.
        for new_super in supers_clone.iter() {
            if let Some(cls) = self.classes.get_mut(new_super.0 as usize) {
                if !cls.direct_subclasses.contains(&id) {
                    cls.direct_subclasses.push(id);
                }
            }
        }

        id
    }

    /// Define a new class (default metaclass, no direct default initargs)
    pub fn define_class(
        &mut self,
        name: SymbolId,
        supers: Vec<ClassId>,
        slots: Vec<SlotDefinition>,
    ) -> ClassId {
        self.define_class_with_meta(name, supers, slots, None, Vec::new())
    }

    /// Find class by name
    pub fn find_class(&self, name: SymbolId) -> Option<ClassId> {
        self.class_names.get(&name).copied()
    }

    /// Get class by ID
    pub fn get_class(&self, id: ClassId) -> Option<&Class> {
        self.classes.get(id.0 as usize)
    }

    /// Get mutable class by ID
    pub fn get_class_mut(&mut self, id: ClassId) -> Option<&mut Class> {
        self.classes.get_mut(id.0 as usize)
    }

    pub fn get_class_direct_slots(&self, id: ClassId) -> Option<&[SlotDefinition]> {
        self.classes
            .get(id.0 as usize)
            .map(|c| c.direct_slots.as_slice())
    }

    pub fn get_class_direct_subclasses(&self, id: ClassId) -> Option<&[ClassId]> {
        self.classes
            .get(id.0 as usize)
            .map(|c| c.direct_subclasses.as_slice())
    }

    pub fn class_ids(&self) -> Vec<ClassId> {
        (0..self.classes.len())
            .map(|i| ClassId(i as u32))
            .collect()
    }

    pub fn get_class_meta_instance(&self, id: ClassId) -> Option<usize> {
        self.class_meta_instances.get(&id).copied()
    }

    pub fn set_class_meta_instance(&mut self, id: ClassId, inst: usize) {
        self.class_meta_instances.insert(id, inst);
    }

    pub fn get_generic_meta_instance(&self, id: GenericId) -> Option<usize> {
        self.generic_meta_instances.get(&id).copied()
    }

    pub fn set_generic_meta_instance(&mut self, id: GenericId, inst: usize) {
        self.generic_meta_instances.insert(id, inst);
    }

    pub fn get_method_meta_instance(&self, id: MethodId) -> Option<usize> {
        self.method_meta_instances.get(&id).copied()
    }

    pub fn set_method_meta_instance(&mut self, id: MethodId, inst: usize) {
        self.method_meta_instances.insert(id, inst);
    }

    pub fn get_slot_def_meta_instance(
        &self,
        class_id: ClassId,
        slot_idx: u32,
        direct: bool,
    ) -> Option<usize> {
        self.slot_def_meta_instances
            .get(&(class_id, slot_idx, direct))
            .copied()
    }

    pub fn set_slot_def_meta_instance(
        &mut self,
        class_id: ClassId,
        slot_idx: u32,
        direct: bool,
        inst: usize,
    ) {
        self.slot_def_meta_instances
            .insert((class_id, slot_idx, direct), inst);
    }

    pub fn add_standalone_slot_def(&mut self, slot: SlotDefinition) -> u32 {
        let idx = self.standalone_slot_defs.len() as u32;
        self.standalone_slot_defs.push(slot);
        idx
    }

    pub fn get_standalone_slot_def(&self, idx: u32) -> Option<&SlotDefinition> {
        self.standalone_slot_defs.get(idx as usize)
    }

    /// Create an instance of a class
    pub fn make_instance(
        &mut self,
        class_id: ClassId,
        default_slot_value: NodeId,
    ) -> Option<usize> {
        let class = self.classes.get(class_id.0 as usize)?;
        let slots = vec![default_slot_value; class.instance_size];

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

    pub fn instance_count(&self) -> usize {
        self.instances.len()
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
        val
    }

    /// Set slot value
    pub fn set_slot_value(&mut self, instance_idx: usize, slot_idx: usize, value: NodeId) {
        if let Some(inst) = self.instances.get_mut(instance_idx) {
            if slot_idx < inst.slots.len() {
                inst.slots[slot_idx] = value;
            } else {
            }
        } else {
        }
    }

    /// Define a generic function (simple form).
    pub fn define_generic(&mut self, name: SymbolId, lambda_list: Vec<SymbolId>) -> GenericId {
        let required_parameters = lambda_list.clone();
        self.define_generic_with_options(name, lambda_list, required_parameters, None)
    }

    /// Define a generic function with lambda-list metadata.
    pub fn define_generic_with_options(
        &mut self,
        name: SymbolId,
        lambda_list: Vec<SymbolId>,
        required_parameters: Vec<SymbolId>,
        argument_precedence_order: Option<Vec<SymbolId>>,
    ) -> GenericId {
        if let Some(&id) = self.generic_names.get(&name) {
            // Update existing generic (keep methods, update lambda list?)
            if let Some(gf) = self.generics.get_mut(id.0 as usize) {
                gf.lambda_list = lambda_list;
                gf.required_parameters = required_parameters;
                gf.argument_precedence_order = argument_precedence_order;
                gf.discriminating_function = None;
                gf.method_cache.clear();
            }
            return id;
        }

        let id = GenericId(self.generics.len() as u32);

        self.generics.push(GenericFunction {
            name,
            lambda_list,
            required_parameters,
            argument_precedence_order,
            discriminating_function: None,
            method_cache: HashMap::new(),
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

    pub fn get_generic_argument_precedence_order(
        &self,
        id: GenericId,
    ) -> Option<&[SymbolId]> {
        self.generics.get(id.0 as usize).and_then(|gf| {
            gf.argument_precedence_order
                .as_ref()
                .map(|order| order.as_slice())
                .or_else(|| Some(gf.required_parameters.as_slice()))
        })
    }

    pub fn get_generic_required_parameters(&self, id: GenericId) -> Option<&[SymbolId]> {
        self.generics
            .get(id.0 as usize)
            .map(|gf| gf.required_parameters.as_slice())
    }

    pub fn get_generic_discriminating_function(&self, id: GenericId) -> Option<NodeId> {
        self.generics
            .get(id.0 as usize)
            .and_then(|gf| gf.discriminating_function)
    }

    pub fn set_generic_discriminating_function(&mut self, id: GenericId, df: NodeId) {
        if let Some(gf) = self.generics.get_mut(id.0 as usize) {
            gf.discriminating_function = Some(df);
        }
    }

    pub fn clear_generic_discriminating_function(&mut self, id: GenericId) {
        if let Some(gf) = self.generics.get_mut(id.0 as usize) {
            gf.discriminating_function = None;
        }
    }

    pub fn get_cached_effective_method(
        &self,
        id: GenericId,
        arg_classes: &[ClassId],
    ) -> Option<NodeId> {
        self.generics.get(id.0 as usize).and_then(|gf| {
            gf.method_cache
                .get(arg_classes)
                .copied()
        })
    }

    pub fn set_cached_effective_method(
        &mut self,
        id: GenericId,
        arg_classes: Vec<ClassId>,
        func: NodeId,
    ) {
        if let Some(gf) = self.generics.get_mut(id.0 as usize) {
            gf.method_cache.insert(arg_classes, func);
        }
    }

    pub fn clear_method_cache(&mut self, id: GenericId) {
        if let Some(gf) = self.generics.get_mut(id.0 as usize) {
            gf.method_cache.clear();
        }
    }

    pub fn set_generic_method_combination(
        &mut self,
        id: GenericId,
        method_combination: MethodCombination,
    ) {
        if let Some(gf) = self.generics.get_mut(id.0 as usize) {
            gf.method_combination = method_combination;
            gf.discriminating_function = None;
            gf.method_cache.clear();
        }
    }

    pub fn register_method_combination(
        &mut self,
        name: SymbolId,
        def: MethodCombinationDef,
    ) {
        self.method_combinations.insert(name, def);
    }

    pub fn get_method_combination(&self, name: SymbolId) -> Option<&MethodCombinationDef> {
        self.method_combinations.get(&name)
    }

    /// Add a method to a generic function
    pub fn add_method(
        &mut self,
        generic_id: GenericId,
        specializers: Vec<Specializer>,
        qualifiers: Vec<SymbolId>,
        lambda_list: Vec<SymbolId>,
        body: NodeId,
    ) -> MethodId {
        let method_id = MethodId(self.methods.len() as u32);

        self.methods.push(Method {
            specializers,
            qualifiers,
            lambda_list,
            body,
            generic: Some(generic_id),
        });

        let new_specs = self.methods[method_id.0 as usize].specializers.clone();
        let new_quals = self.methods[method_id.0 as usize].qualifiers.clone();

        let existing_pos = self
            .generics
            .get(generic_id.0 as usize)
            .and_then(|gf| {
                gf.methods.iter().position(|mid| {
                    if let Some(m) = self.methods.get(mid.0 as usize) {
                        m.specializers == new_specs && m.qualifiers == new_quals
                    } else {
                        false
                    }
                })
            });

        if let Some(gf) = self.generics.get_mut(generic_id.0 as usize) {
            if let Some(pos) = existing_pos {
                gf.methods.remove(pos);
            }
            gf.methods.push(method_id);
            gf.discriminating_function = None;
            gf.method_cache.clear();
        }

        method_id
    }

    /// Add a method without attaching it to a generic function (used for wrappers).
    pub fn add_method_raw(
        &mut self,
        specializers: Vec<Specializer>,
        qualifiers: Vec<SymbolId>,
        body: NodeId,
    ) -> MethodId {
        let method_id = MethodId(self.methods.len() as u32);
        self.methods.push(Method {
            specializers,
            qualifiers,
            lambda_list: Vec::new(),
            body,
            generic: None,
        });
        method_id
    }

    /// Get method by ID
    pub fn get_method(&self, id: MethodId) -> Option<&Method> {
        self.methods.get(id.0 as usize)
    }

    pub fn get_method_qualifiers(&self, id: MethodId) -> Option<&[SymbolId]> {
        self.methods.get(id.0 as usize).map(|m| m.qualifiers.as_slice())
    }

    pub fn get_method_specializers(&self, id: MethodId) -> Option<&[Specializer]> {
        self.methods
            .get(id.0 as usize)
            .map(|m| m.specializers.as_slice())
    }

    pub fn get_method_lambda_list(&self, id: MethodId) -> Option<&[SymbolId]> {
        self.methods
            .get(id.0 as usize)
            .map(|m| m.lambda_list.as_slice())
    }

    pub fn get_method_generic(&self, id: MethodId) -> Option<GenericId> {
        self.methods.get(id.0 as usize).and_then(|m| m.generic)
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

    pub fn get_eql_specializer_object(&self, idx: u32) -> Option<NodeId> {
        self.eql_specializers
            .get(idx as usize)
            .map(|s| s.object)
    }

    pub fn intern_eql_specializer(&mut self, arena: &Arena, object: NodeId) -> u32 {
        for (idx, spec) in self.eql_specializers.iter().enumerate() {
            if self.eql_nodes(arena, spec.object, object) {
                return idx as u32;
            }
        }
        let idx = self.eql_specializers.len() as u32;
        self.eql_specializers.push(EqlSpecializer { object });
        idx
    }

    pub fn generic_uses_eql_specializers(&self, generic_id: GenericId) -> bool {
        if let Some(gf) = self.get_generic(generic_id) {
            for &mid in &gf.methods {
                if let Some(method) = self.get_method(mid) {
                    if method
                        .specializers
                        .iter()
                        .any(|s| matches!(s, Specializer::Eql(_)))
                    {
                        return true;
                    }
                }
            }
        }
        false
    }

    fn class_of_node(&self, node: NodeId, arena: &Arena) -> ClassId {
        match arena.get_unchecked(node) {
            Node::Leaf(OpaqueValue::Instance(id)) => self
                .get_instance(*id as usize)
                .map(|i| i.class)
                .unwrap_or(self.standard_object),
            Node::Leaf(OpaqueValue::Class(_)) => self.standard_class,
            Node::Leaf(OpaqueValue::Symbol(_)) => self.symbol_class,
            Node::Leaf(OpaqueValue::Integer(_)) => self.integer_class,
            Node::Leaf(OpaqueValue::Generic(_)) => self.standard_generic_function,
            Node::Leaf(OpaqueValue::Method(_)) => self.standard_method,
            Node::Leaf(OpaqueValue::SlotDefinition(_, _, direct)) => {
                if *direct {
                    self.standard_direct_slot_definition
                } else {
                    self.standard_effective_slot_definition
                }
            }
            Node::Leaf(OpaqueValue::EqlSpecializer(_)) => self.eql_specializer_class,
            _ => self.t_class,
        }
    }

    fn eql_nodes(&self, arena: &Arena, a: NodeId, b: NodeId) -> bool {
        if a == b {
            return true;
        }

        match (arena.get_unchecked(a), arena.get_unchecked(b)) {
            (Node::Leaf(OpaqueValue::Integer(ai)), Node::Leaf(OpaqueValue::Integer(bi))) => {
                return ai == bi;
            }
            (Node::Leaf(OpaqueValue::BigInt(ai)), Node::Leaf(OpaqueValue::BigInt(bi))) => {
                return ai == bi;
            }
            (Node::Leaf(OpaqueValue::Float(af)), Node::Leaf(OpaqueValue::Float(bf))) => {
                return af == bf;
            }
            (Node::Leaf(OpaqueValue::Integer(ai)), Node::Leaf(OpaqueValue::Float(bf))) => {
                return (*ai as f64) == *bf;
            }
            (Node::Leaf(OpaqueValue::Float(af)), Node::Leaf(OpaqueValue::Integer(bi))) => {
                return *af == (*bi as f64);
            }
            (Node::Leaf(OpaqueValue::BigInt(ai)), Node::Leaf(OpaqueValue::Float(bf))) => {
                return ai.to_f64().unwrap_or(f64::INFINITY) == *bf;
            }
            (Node::Leaf(OpaqueValue::Float(af)), Node::Leaf(OpaqueValue::BigInt(bi))) => {
                return *af == bi.to_f64().unwrap_or(f64::INFINITY);
            }
            (Node::Leaf(OpaqueValue::Integer(ai)), Node::Leaf(OpaqueValue::BigInt(bi))) => {
                return num_bigint::BigInt::from(*ai) == *bi;
            }
            (Node::Leaf(OpaqueValue::BigInt(ai)), Node::Leaf(OpaqueValue::Integer(bi))) => {
                return *ai == num_bigint::BigInt::from(*bi);
            }
            _ => {}
        }

        match (arena.get_unchecked(a), arena.get_unchecked(b)) {
            (Node::Leaf(OpaqueValue::Symbol(id1)), Node::Leaf(OpaqueValue::Symbol(id2))) => {
                id1 == id2
            }
            (Node::Leaf(OpaqueValue::Class(id1)), Node::Leaf(OpaqueValue::Class(id2))) => {
                id1 == id2
            }
            (Node::Leaf(OpaqueValue::Instance(id1)), Node::Leaf(OpaqueValue::Instance(id2))) => {
                id1 == id2
            }
            (Node::Leaf(OpaqueValue::Generic(id1)), Node::Leaf(OpaqueValue::Generic(id2))) => {
                id1 == id2
            }
            (Node::Leaf(OpaqueValue::Method(id1)), Node::Leaf(OpaqueValue::Method(id2))) => {
                id1 == id2
            }
            (Node::Leaf(OpaqueValue::EqlSpecializer(id1)), Node::Leaf(OpaqueValue::EqlSpecializer(id2))) => {
                id1 == id2
            }
            (
                Node::Leaf(OpaqueValue::SlotDefinition(c1, s1, d1)),
                Node::Leaf(OpaqueValue::SlotDefinition(c2, s2, d2)),
            ) => c1 == c2 && s1 == s2 && d1 == d2,
            (Node::Leaf(OpaqueValue::Nil), Node::Leaf(OpaqueValue::Nil)) => true,
            _ => false,
        }
    }

    fn method_applicable_values(
        &self,
        method: &Method,
        arg_values: &[NodeId],
        arg_classes: &[ClassId],
        arena: &Arena,
    ) -> bool {
        if method.specializers.len() > arg_values.len() {
            return false;
        }

        for (i, spec) in method.specializers.iter().enumerate() {
            match spec {
                Specializer::Class(class_id) => {
                    if let Some(&arg_class) = arg_classes.get(i) {
                        if let Some(class) = self.classes.get(arg_class.0 as usize) {
                            if !class.cpl.contains(class_id) {
                                return false;
                            }
                        } else {
                            return false;
                        }
                    } else {
                        return false;
                    }
                }
                Specializer::Eql(idx) => {
                    let obj = match self.get_eql_specializer_object(*idx) {
                        Some(obj) => obj,
                        None => return false,
                    };
                    let arg = match arg_values.get(i) {
                        Some(v) => *v,
                        None => return false,
                    };
                    if !self.eql_nodes(arena, obj, arg) {
                        return false;
                    }
                }
            }
        }

        true
    }

    fn method_applicable_classes(&self, method: &Method, arg_classes: &[ClassId]) -> bool {
        if method
            .specializers
            .iter()
            .any(|s| matches!(s, Specializer::Eql(_)))
        {
            return false;
        }

        if method.specializers.len() > arg_classes.len() {
            return false;
        }

        for (i, spec) in method.specializers.iter().enumerate() {
            let class_id = match spec {
                Specializer::Class(cid) => cid,
                Specializer::Eql(_) => return false,
            };
            if let Some(&arg_class) = arg_classes.get(i) {
                if let Some(class) = self.classes.get(arg_class.0 as usize) {
                    if !class.cpl.contains(class_id) {
                        return false;
                    }
                } else {
                    return false;
                }
            }
        }

        true
    }

    /// Find applicable methods for given argument values
    pub fn compute_applicable_methods(
        &self,
        generic_id: GenericId,
        arg_values: &[NodeId],
        arena: &Arena,
    ) -> Vec<MethodId> {
        let gf = match self.get_generic(generic_id) {
            Some(gf) => gf,
            None => return Vec::new(),
        };

        let arg_classes: Vec<ClassId> = arg_values
            .iter()
            .map(|&v| self.class_of_node(v, arena))
            .collect();

        let mut applicable = Vec::new();

        for &method_id in &gf.methods {
            if let Some(method) = self.get_method(method_id) {
                if self.method_applicable_values(method, arg_values, &arg_classes, arena) {
                    applicable.push(method_id);
                }
            }
        }

        let order = self.argument_precedence_order_indices(generic_id);

        // Sort by specificity (most specific first)
        applicable.sort_by(|&a, &b| {
            let ma = self.get_method(a).unwrap();
            let mb = self.get_method(b).unwrap();
            self.compare_method_specificity(ma, mb, &arg_classes, &order)
        });

        applicable
    }

    /// Find applicable methods for given argument classes (EQL specializers ignored)
    pub fn compute_applicable_methods_using_classes(
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
                if self.method_applicable_classes(method, arg_classes) {
                    applicable.push(method_id);
                }
            }
        }

        let order = self.argument_precedence_order_indices(generic_id);

        applicable.sort_by(|&a, &b| {
            let ma = self.get_method(a).unwrap();
            let mb = self.get_method(b).unwrap();
            self.compare_method_specificity(ma, mb, arg_classes, &order)
        });

        applicable
    }

    fn argument_precedence_order_indices(&self, generic_id: GenericId) -> Vec<usize> {
        let gf = match self.get_generic(generic_id) {
            Some(gf) => gf,
            None => return Vec::new(),
        };

        let required = &gf.required_parameters;
        let order_syms = gf
            .argument_precedence_order
            .as_ref()
            .unwrap_or(required);

        let mut indices = Vec::new();
        for sym in order_syms {
            if let Some(idx) = required.iter().position(|s| s == sym) {
                indices.push(idx);
            }
        }

        if indices.is_empty() {
            indices = (0..required.len()).collect();
        }

        indices
    }

    fn compare_method_specificity(
        &self,
        ma: &Method,
        mb: &Method,
        arg_classes: &[ClassId],
        order: &[usize],
    ) -> std::cmp::Ordering {
        // Compare based on argument class precedence lists (most specific first).
        let indices: Vec<usize> = if order.is_empty() {
            (0..arg_classes.len()).collect()
        } else {
            order.to_vec()
        };

        for &i in &indices {
            let arg_class = match arg_classes.get(i) {
                Some(class) => class,
                None => continue,
            };
            let cpl = match self.classes.get(arg_class.0 as usize) {
                Some(c) => &c.cpl,
                None => continue,
            };

            let sa = ma
                .specializers
                .get(i)
                .cloned()
                .unwrap_or(Specializer::Class(self.t_class));
            let sb = mb
                .specializers
                .get(i)
                .cloned()
                .unwrap_or(Specializer::Class(self.t_class));

            match (&sa, &sb) {
                (Specializer::Eql(_), Specializer::Class(_)) => {
                    return std::cmp::Ordering::Less;
                }
                (Specializer::Class(_), Specializer::Eql(_)) => {
                    return std::cmp::Ordering::Greater;
                }
                (Specializer::Eql(_), Specializer::Eql(_)) => {
                    continue;
                }
                (Specializer::Class(ca), Specializer::Class(cb)) => {
                    let posa = cpl.iter().position(|c| *c == *ca).unwrap_or(usize::MAX);
                    let posb = cpl.iter().position(|c| *c == *cb).unwrap_or(usize::MAX);

                    if posa != posb {
                        return posa.cmp(&posb);
                    }
                }
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
                if let Some(initfn) = slot.initfunction {
                    roots.push(initfn);
                }
                if let Some(slot_type) = slot.slot_type {
                    roots.push(slot_type);
                }
                if let Some(class_val) = slot.class_value {
                    roots.push(class_val);
                }
            }
        }

        // Trace Methods (bodies)
        for method in &self.methods {
            roots.push(method.body);
        }

        // Trace registered method combination expanders
        for def in self.method_combinations.values() {
            if let MethodCombinationDef::Long { expander } = def {
                roots.push(*expander);
            }
        }

        // Trace method combination options/expanders stored on generics
        for gf in &self.generics {
            if let MethodCombination::UserLong { expander, options, .. } = gf.method_combination {
                roots.push(expander);
                roots.push(options);
            }
            if let Some(df) = gf.discriminating_function {
                roots.push(df);
            }
            for func in gf.method_cache.values() {
                roots.push(*func);
            }
        }

        // Trace interned EQL specializers
        for spec in &self.eql_specializers {
            roots.push(spec.object);
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
                    initfunction: None,
                    initarg: None,
                    readers: Vec::new(),
                    writers: Vec::new(),
                    allocation: SlotAllocation::Instance,
                    slot_type: None,
                    class_value: None,
                    index: 0,
                },
                SlotDefinition {
                    name: y_name,
                    initform: None,
                    initfunction: None,
                    initarg: None,
                    readers: Vec::new(),
                    writers: Vec::new(),
                    allocation: SlotAllocation::Instance,
                    slot_type: None,
                    class_value: None,
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
                initfunction: None,
                initarg: None,
                readers: Vec::new(),
                writers: Vec::new(),
                allocation: SlotAllocation::Instance,
                slot_type: None,
                class_value: None,
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
                initfunction: None,
                initarg: None,
                readers: Vec::new(),
                writers: Vec::new(),
                allocation: SlotAllocation::Instance,
                slot_type: None,
                class_value: None,
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
