use std::ffi::c_void;

pub use crate::symbol::SymbolId;

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct NodeId(pub u32);

#[derive(Clone, Debug, PartialEq)] // Removed Copy because StringHandle/VectorHandle might imply ownership semantics later, but for now they are indices.
pub enum OpaqueValue {
    Nil,
    Integer(i64),
    Float(f64),
    String(String),          // String content
    Closure(u32),            // Handle to Closure
    VectorHandle(u32),       // Index into Vector Storage
    ForeignPtr(*mut c_void), // FFI Handle
    Generic(u32),            // Handle to Generic Function (CLOS)
    Instance(u32),           // Handle to Instance (CLOS)
    Class(u32),              // Handle to Class (CLOS)
    Symbol(u32),             // Symbol ID
    BigInt(num_bigint::BigInt), // Arbitrary precision integer
    StreamHandle(u32),       // Handle to Stream
}

// Implement partial_cmp for Float to allow it in some contexts (careful with NaN)
impl PartialOrd for OpaqueValue {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        use num_traits::ToPrimitive;
        match (self, other) {
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
            (OpaqueValue::BigInt(a), OpaqueValue::Float(b)) => a.to_f64().unwrap_or(f64::INFINITY).partial_cmp(b),
            (OpaqueValue::Float(a), OpaqueValue::BigInt(b)) => a.partial_cmp(&b.to_f64().unwrap_or(f64::INFINITY)),
            _ => None, 
        }
    }
}
