# ptr_eq

[WIP] by-address comparisons and hashes in Rust.

## Motivation

It is a common practice to identify an object by its address. Many programming languages 
with non-trivial runtime have native support for this pattern. For example, in Java and
Python, two references are equal if they point to the same object. Even in system 
programming languages like C++, one may achieve this by using smart pointers like
`std::unique_ptr` and `std::shared_ptr`, or just using raw pointers. The equality of 
these types is always determined by the pointer value.

This is, however, not the case in Rust. For example, in the default comparison 
implementation for `&T` compares the pointees, rather than the addresses. Smart pointers, 
like `std::rc::Rc` and `std::sync::Arc`, do so, as well. Only raw pointers, which are unsafe
to use, compare by address. Typically, one should invoke special functions like
`std::ptr::eq` to compare by address. This makes it inconvenient to determine the identity
of two references by address.

This crate defines a trait `PtrEq` to indicate that references to this object compare 
equality by address. It also provides procedure macros to automatically derive these 
implementations, overriding the default Rust reference comparison rules.
