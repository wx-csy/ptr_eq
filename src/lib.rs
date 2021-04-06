extern crate ptr_eq_macros;

pub mod rc;

pub use ptr_eq_macros::PtrEq;

/// A marker trait for types that implement by-address comparisons, equality tests,
/// and hashes.
pub unsafe trait PtrEq {}
