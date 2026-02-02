use std::ffi::c_void;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)] // Added Copy/Clone/Eq/Hash
pub struct ForeignHandle(pub *mut c_void);

unsafe impl Send for ForeignHandle {}
unsafe impl Sync for ForeignHandle {}

pub use crate::symbol::SymbolId;

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct NodeId(pub u32);

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct HashHandle(pub u32);

#[derive(Clone, Debug, PartialEq)] // Removed Copy because StringHandle/VectorHandle might imply ownership semantics later, but for now they are indices.
pub enum OpaqueValue {
    Nil,
    Unbound,
    Integer(i64),
    Float(f64),
    String(String),             // String content
    Closure(u32),               // Handle to Closure
    VectorHandle(u32),          // Index into Vector Storage
    ForeignPtr(ForeignHandle),  // FFI Handle
    Generic(u32),               // Handle to Generic Function (CLOS)
    Instance(u32),              // Handle to Instance (CLOS)
    Class(u32),                 // Handle to Class (CLOS)
    Symbol(u32),                // Symbol ID
    BigInt(num_bigint::BigInt), // Arbitrary precision integer
    StreamHandle(u32),          // Handle to Stream
    Pid(crate::process::Pid),   // Process ID
    HashHandle(u32),            // Handle to Hash Table
    Package(u32),               // Package ID
    NextMethod(u32),            // Handle to Next Method State (CLOS)
    NextMethodP(u32),           // Handle to Next Method State predicate (CLOS)
    CallMethod(u32),            // Handle to Call-Method state (CLOS)
    MethodWrapper(u32, u32),    // (ClosureIndex, NextMethodIndex)
    Method(u32),                // Handle to Method (CLOS)
    EqlSpecializer(u32),        // Handle to EQL specializer (CLOS)
    SlotDefinition(u32, u32, bool), // (ClassId, SlotIndex, Direct?)
}

// Implement partial_cmp for Float to allow it in some contexts (careful with NaN)
impl PartialOrd for OpaqueValue {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        use num_traits::ToPrimitive;
        match (self, other) {
            (OpaqueValue::Pid(a), OpaqueValue::Pid(b)) => {
                // Lexicographical comparison for PIDs
                match a.node.partial_cmp(&b.node) {
                    Some(core::cmp::Ordering::Equal) => match a.id.partial_cmp(&b.id) {
                        Some(core::cmp::Ordering::Equal) => a.serial.partial_cmp(&b.serial),
                        other => other,
                    },
                    other => other,
                }
            }
            (OpaqueValue::Integer(a), OpaqueValue::Integer(b)) => a.partial_cmp(b),
            (OpaqueValue::BigInt(a), OpaqueValue::BigInt(b)) => a.partial_cmp(b),
            (OpaqueValue::Integer(a), OpaqueValue::BigInt(b)) => {
                num_bigint::BigInt::from(*a).partial_cmp(b)
            }
            (OpaqueValue::BigInt(a), OpaqueValue::Integer(b)) => {
                a.partial_cmp(&num_bigint::BigInt::from(*b))
            }
            // Mixed Float/Int comparisons
            (OpaqueValue::Float(a), OpaqueValue::Float(b)) => a.partial_cmp(b),
            (OpaqueValue::Integer(a), OpaqueValue::Float(b)) => (*a as f64).partial_cmp(b),
            (OpaqueValue::Float(a), OpaqueValue::Integer(b)) => a.partial_cmp(&(*b as f64)),
            (OpaqueValue::BigInt(a), OpaqueValue::Float(b)) => {
                a.to_f64().unwrap_or(f64::INFINITY).partial_cmp(b)
            }
            (OpaqueValue::Float(a), OpaqueValue::BigInt(b)) => {
                a.partial_cmp(&b.to_f64().unwrap_or(f64::INFINITY))
            }
            _ => None,
        }
    }
}
