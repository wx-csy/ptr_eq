#[macro_use]
extern crate ptr_eq_macro;
pub mod rc;

/// A marker trait for types that implement by-address comparisons, equality tests,
/// and hashes.
pub unsafe trait PtrEq { }

#[derive(PtrEq)]
pub struct Test(i32);

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}
