//! Single-threaded reference-counting pointers. 'Rc' stands for 'Reference
//! Counted'.
//!
//! The type [`Rc<T>`][`Rc`] provides shared ownership of a value of type `T`,
//! allocated in the heap. Invoking [`clone`][clone] on [`Rc`] produces a new
//! pointer to the same allocation in the heap. When the last [`Rc`] pointer to a
//! given allocation is destroyed, the value stored in that allocation (often
//! referred to as "inner value") is also dropped.
//!
//! Shared references in Rust disallow mutation by default, and [`Rc`]
//! is no exception: you cannot generally obtain a mutable reference to
//! something inside an [`Rc`]. If you need mutability, put a [`Cell`]
//! or [`RefCell`] inside the [`Rc`]; see [an example of mutability
//! inside an `Rc`][mutability].
//!
//! [`Rc`] uses non-atomic reference counting. This means that overhead is very
//! low, but an [`Rc`] cannot be sent between threads, and consequently [`Rc`]
//! does not implement [`Send`][send]. As a result, the Rust compiler
//! will check *at compile time* that you are not sending [`Rc`]s between
//! threads. If you need multi-threaded, atomic reference counting, use
//! [`sync::Arc`][arc].
//!
//! The [`downgrade`][downgrade] method can be used to create a non-owning
//! [`Weak`] pointer. A [`Weak`] pointer can be [`upgrade`][upgrade]d
//! to an [`Rc`], but this will return [`None`] if the value stored in the allocation has
//! already been dropped. In other words, `Weak` pointers do not keep the value
//! inside the allocation alive; however, they *do* keep the allocation
//! (the backing store for the inner value) alive.
//!
//! A cycle between [`Rc`] pointers will never be deallocated. For this reason,
//! [`Weak`] is used to break cycles. For example, a tree could have strong
//! [`Rc`] pointers from parent nodes to children, and [`Weak`] pointers from
//! children back to their parents.
//!
//! `Rc<T>` automatically dereferences to `T` (via the [`Deref`] trait),
//! so you can call `T`'s methods on a value of type [`Rc<T>`][`Rc`]. To avoid name
//! clashes with `T`'s methods, the methods of [`Rc<T>`][`Rc`] itself are associated
//! functions, called using [fully qualified syntax]:
//!
//! ```
//! use std::rc::Rc;
//!
//! let my_rc = Rc::new(());
//! Rc::downgrade(&my_rc);
//! ```
//!
//! `Rc<T>`'s implementations of traits like `Clone` may also be called using
//! fully qualified syntax. Some people prefer to use fully qualified syntax,
//! while others prefer using method-call syntax.
//!
//! ```
//! use std::rc::Rc;
//!
//! let rc = Rc::new(());
//! // Method-call syntax
//! let rc2 = rc.clone();
//! // Fully qualified syntax
//! let rc3 = Rc::clone(&rc);
//! ```
//!
//! [`Weak<T>`][`Weak`] does not auto-dereference to `T`, because the inner value may have
//! already been dropped.
//!
//! # Cloning references
//!
//! Creating a new reference to the same allocation as an existing reference counted pointer
//! is done using the `Clone` trait implemented for [`Rc<T>`][`Rc`] and [`Weak<T>`][`Weak`].
//!
//! ```
//! use ptr_eq::rc::Rc;
//! use ptr_eq::PtrEq;
//! 
//! #[derive(PtrEq, Debug)]
//! struct Test(i64);
//!
//! let foo = Rc::new(Test(42));
//! // The two syntaxes below are equivalent.
//! let a = foo.clone();
//! let b = Rc::clone(&foo);
//! // a and b both point to the same memory location as foo.
//! ```
//!
//! The `Rc::clone(&from)` syntax is the most idiomatic because it conveys more explicitly
//! the meaning of the code. In the example above, this syntax makes it easier to see that
//! this code is creating a new reference rather than copying the whole content of foo.
//!
//! # Examples
//!
//! Consider a scenario where a set of `Gadget`s are owned by a given `Owner`.
//! We want to have our `Gadget`s point to their `Owner`. We can't do this with
//! unique ownership, because more than one gadget may belong to the same
//! `Owner`. [`Rc`] allows us to share an `Owner` between multiple `Gadget`s,
//! and have the `Owner` remain allocated as long as any `Gadget` points at it.
//!
//! ```
//! use ptr_eq::rc::Rc;
//! use ptr_eq::PtrEq;
//!
//! #[derive(PtrEq)]
//! struct Owner {
//!     name: String,
//!     // ...other fields
//! }
//!
//! struct Gadget {
//!     id: i32,
//!     owner: Rc<Owner>,
//!     // ...other fields
//! }
//!
//! fn main() {
//!     // Create a reference-counted `Owner`.
//!     let gadget_owner: Rc<Owner> = Rc::new(
//!         Owner {
//!             name: "Gadget Man".to_string(),
//!         }
//!     );
//!
//!     // Create `Gadget`s belonging to `gadget_owner`. Cloning the `Rc<Owner>`
//!     // gives us a new pointer to the same `Owner` allocation, incrementing
//!     // the reference count in the process.
//!     let gadget1 = Gadget {
//!         id: 1,
//!         owner: Rc::clone(&gadget_owner),
//!     };
//!     let gadget2 = Gadget {
//!         id: 2,
//!         owner: Rc::clone(&gadget_owner),
//!     };
//!
//!     // Dispose of our local variable `gadget_owner`.
//!     drop(gadget_owner);
//!
//!     // Despite dropping `gadget_owner`, we're still able to print out the name
//!     // of the `Owner` of the `Gadget`s. This is because we've only dropped a
//!     // single `Rc<Owner>`, not the `Owner` it points to. As long as there are
//!     // other `Rc<Owner>` pointing at the same `Owner` allocation, it will remain
//!     // live. The field projection `gadget1.owner.name` works because
//!     // `Rc<Owner>` automatically dereferences to `Owner`.
//!     println!("Gadget {} owned by {}", gadget1.id, gadget1.owner.name);
//!     println!("Gadget {} owned by {}", gadget2.id, gadget2.owner.name);
//!
//!     // At the end of the function, `gadget1` and `gadget2` are destroyed, and
//!     // with them the last counted references to our `Owner`. Gadget Man now
//!     // gets destroyed as well.
//! }
//! ```
//!
//! If our requirements change, and we also need to be able to traverse from
//! `Owner` to `Gadget`, we will run into problems. An [`Rc`] pointer from `Owner`
//! to `Gadget` introduces a cycle. This means that their
//! reference counts can never reach 0, and the allocation will never be destroyed:
//! a memory leak. In order to get around this, we can use [`Weak`]
//! pointers.
//!
//! Rust actually makes it somewhat difficult to produce this loop in the first
//! place. In order to end up with two values that point at each other, one of
//! them needs to be mutable. This is difficult because [`Rc`] enforces
//! memory safety by only giving out shared references to the value it wraps,
//! and these don't allow direct mutation. We need to wrap the part of the
//! value we wish to mutate in a [`RefCell`], which provides *interior
//! mutability*: a method to achieve mutability through a shared reference.
//! [`RefCell`] enforces Rust's borrowing rules at runtime.
//!
//! ```
//! use ptr_eq::rc::{Rc, Weak};
//! use ptr_eq::PtrEq;
//! use std::cell::RefCell;
//!
//! #[derive(PtrEq)]
//! struct Owner {
//!     name: String,
//!     gadgets: RefCell<Vec<Weak<Gadget>>>,
//!     // ...other fields
//! }
//!
//! #[derive(PtrEq)]
//! struct Gadget {
//!     id: i32,
//!     owner: Rc<Owner>,
//!     // ...other fields
//! }
//!
//! fn main() {
//!     // Create a reference-counted `Owner`. Note that we've put the `Owner`'s
//!     // vector of `Gadget`s inside a `RefCell` so that we can mutate it through
//!     // a shared reference.
//!     let gadget_owner: Rc<Owner> = Rc::new(
//!         Owner {
//!             name: "Gadget Man".to_string(),
//!             gadgets: RefCell::new(vec![]),
//!         }
//!     );
//!
//!     // Create `Gadget`s belonging to `gadget_owner`, as before.
//!     let gadget1 = Rc::new(
//!         Gadget {
//!             id: 1,
//!             owner: Rc::clone(&gadget_owner),
//!         }
//!     );
//!     let gadget2 = Rc::new(
//!         Gadget {
//!             id: 2,
//!             owner: Rc::clone(&gadget_owner),
//!         }
//!     );
//!
//!     // Add the `Gadget`s to their `Owner`.
//!     {
//!         let mut gadgets = gadget_owner.gadgets.borrow_mut();
//!         gadgets.push(Rc::downgrade(&gadget1));
//!         gadgets.push(Rc::downgrade(&gadget2));
//!
//!         // `RefCell` dynamic borrow ends here.
//!     }
//!
//!     // Iterate over our `Gadget`s, printing their details out.
//!     for gadget_weak in gadget_owner.gadgets.borrow().iter() {
//!
//!         // `gadget_weak` is a `Weak<Gadget>`. Since `Weak` pointers can't
//!         // guarantee the allocation still exists, we need to call
//!         // `upgrade`, which returns an `Option<Rc<Gadget>>`.
//!         //
//!         // In this case we know the allocation still exists, so we simply
//!         // `unwrap` the `Option`. In a more complicated program, you might
//!         // need graceful error handling for a `None` result.
//!
//!         let gadget = gadget_weak.upgrade().unwrap();
//!         println!("Gadget {} owned by {}", gadget.id, gadget.owner.name);
//!     }
//!
//!     // At the end of the function, `gadget_owner`, `gadget1`, and `gadget2`
//!     // are destroyed. There are now no strong (`Rc`) pointers to the
//!     // gadgets, so they are destroyed. This zeroes the reference count on
//!     // Gadget Man, so he gets destroyed as well.
//! }
//! ```
//!
//! [clone]: Clone::clone
//! [`Cell`]: core::cell::Cell
//! [`RefCell`]: core::cell::RefCell
//! [send]: core::marker::Send
//! [arc]: crate::sync::Arc
//! [`Deref`]: core::ops::Deref
//! [downgrade]: Rc::downgrade
//! [upgrade]: Weak::upgrade
//! [mutability]: core::cell#introducing-mutability-inside-of-something-immutable
//! [fully qualified syntax]: https://doc.rust-lang.org/book/ch19-03-advanced-traits.html#fully-qualified-syntax-for-disambiguation-calling-methods-with-the-same-name


use crate::PtrEq;
use core::{borrow::Borrow, fmt};
use std::{iter, ops::Deref, pin::Pin, rc::Rc as StdRc, rc::Weak as StdWeak};

/// A single-threaded reference-counting pointer. 'Rc' stands for 'Reference
/// Counted'.
///
/// See the [module-level documentation](./index.html) for more details.
///
/// The inherent methods of `Rc` are all associated functions, which means
/// that you have to call them as e.g., [`Rc::get_mut(&mut value)`][get_mut] instead of
/// `value.get_mut()`. This avoids conflicts with methods of the inner type `T`.
///
/// [get_mut]: Rc::get_mut
#[repr(transparent)]
#[derive(Debug)]
pub struct Rc<T: PtrEq + ?Sized>(StdRc<T>);

impl<T: PtrEq> Rc<T> {
    /// Constructs a new `Rc<T>`.
    ///
    /// # Examples
    ///
    /// ```
    /// use ptr_eq::rc::Rc;
    /// use ptr_eq::PtrEq;
    /// 
    /// #[derive(PtrEq)]
    /// struct Test(i64);
    /// 
    /// let five = Rc::new(Test(5));
    /// ```
    #[inline]
    pub fn new(value: T) -> Rc<T> {
        Rc(StdRc::new(value))
    }

    /// Constructs a new `Pin<Rc<T>>`. If `T` does not implement `Unpin`, then
    /// `value` will be pinned in memory and unable to be moved.
    #[inline]
    pub fn pin(value: T) -> Pin<Rc<T>> {
        unsafe { Pin::new_unchecked(Rc::new(value)) }
    }

    /// Returns the inner value, if the `Rc` has exactly one strong reference.
    ///
    /// Otherwise, an [`Err`] is returned with the same `Rc` that was
    /// passed in.
    ///
    /// This will succeed even if there are outstanding weak references.
    ///
    /// # Examples
    ///
    /// ```
    /// use ptr_eq::rc::Rc;
    /// use ptr_eq::PtrEq;
    /// 
    /// #[derive(PtrEq, Debug)]
    /// struct Test(i64);
    ///
    /// let x = Rc::new(Test(3));
    /// assert_eq!(Rc::try_unwrap(x).unwrap().0, 3);
    ///
    /// let x = Rc::new(Test(4));
    /// let _y = Rc::clone(&x);
    /// assert_eq!(Rc::try_unwrap(x).unwrap_err().0, 4);
    /// ```
    #[inline]
    pub fn try_unwrap(this: Self) -> Result<T, Self> {
        StdRc::try_unwrap(this.0).or_else(|ret| Err(Rc(ret)))
    }
}

impl<T: PtrEq + ?Sized> Rc<T> {
    /// Consumes the `Rc`, returning the wrapped pointer.
    ///
    /// To avoid a memory leak the pointer must be converted back to an `Rc` using
    /// [`Rc::from_raw`][from_raw].
    ///
    /// [from_raw]: Rc::from_raw
    ///
    /// # Examples
    ///
    /// ```
    /// use ptr_eq::rc::Rc;
    /// use ptr_eq::PtrEq;
    /// 
    /// #[derive(PtrEq, Debug)]
    /// struct Test(i64);
    /// 
    /// let x = Rc::new(Test(42));
    /// let x_ptr = Rc::into_raw(x);
    /// assert_eq!(unsafe { &*x_ptr }.0, 42);
    /// ```
    #[inline]
    pub fn into_raw(this: Self) -> *const T {
        StdRc::into_raw(this.0)
    }

    /// Provides a raw pointer to the data.
    ///
    /// The counts are not affected in any way and the `Rc` is not consumed. The pointer is valid
    /// for as long there are strong counts in the `Rc`.
    ///
    /// # Examples
    ///
    /// ```
    /// use ptr_eq::rc::Rc;
    /// use ptr_eq::PtrEq;
    /// 
    /// #[derive(PtrEq, Debug)]
    /// struct Test(i64);
    ///
    /// let x = Rc::new(Test(42));
    /// let y = Rc::clone(&x);
    /// let x_ptr = Rc::as_ptr(&x);
    /// assert_eq!(x_ptr, Rc::as_ptr(&y));
    /// assert_eq!(unsafe { &*x_ptr }.0, 42);
    /// ```
    #[inline]
    pub fn as_ptr(this: &Self) -> *const T {
        StdRc::as_ptr(&this.0)
    }

    /// Constructs an `Rc<T>` from a raw pointer.
    ///
    /// The raw pointer must have been previously returned by a call to
    /// [`Rc<U>::into_raw`][into_raw] where `U` must have the same size
    /// and alignment as `T`. This is trivially true if `U` is `T`.
    /// Note that if `U` is not `T` but has the same size and alignment, this is
    /// basically like transmuting references of different types. See
    /// [`mem::transmute`][transmute] for more information on what
    /// restrictions apply in this case.
    ///
    /// The user of `from_raw` has to make sure a specific value of `T` is only
    /// dropped once.
    ///
    /// This function is unsafe because improper use may lead to memory unsafety,
    /// even if the returned `Rc<T>` is never accessed.
    ///
    /// [into_raw]: Rc::into_raw
    /// [transmute]: core::mem::transmute
    ///
    /// # Examples
    ///
    /// ```
    /// use ptr_eq::rc::Rc;
    /// use ptr_eq::PtrEq;
    /// 
    /// #[derive(PtrEq, Debug)]
    /// struct Test(i64);
    /// 
    /// let x = Rc::new(Test(42));
    /// let x_ptr = Rc::into_raw(x);
    ///
    /// unsafe {
    ///     // Convert back to an `Rc` to prevent leak.
    ///     let x = Rc::from_raw(x_ptr);
    ///     assert_eq!(x.0, 42);
    ///
    ///     // Further calls to `Rc::from_raw(x_ptr)` would be memory-unsafe.
    /// }
    ///
    /// // The memory was freed when `x` went out of scope above, so `x_ptr` is now dangling!
    /// ```
    #[inline]
    pub unsafe fn from_raw(ptr: *const T) -> Self {
        Rc(StdRc::from_raw(ptr))
    }

    /// Creates a new [`Weak`] pointer to this allocation.
    ///
    /// # Examples
    ///
    /// ```
    /// use ptr_eq::rc::Rc;
    /// use ptr_eq::PtrEq;
    /// 
    /// #[derive(PtrEq, Debug)]
    /// struct Test(i64);
    /// 
    /// let five = Rc::new(Test(5));
    ///
    /// let weak_five = Rc::downgrade(&five);
    /// ```
    #[inline]
    pub fn downgrade(this: &Self) -> Weak<T> {
        Weak(StdRc::downgrade(&this.0))
    }

    /// Gets the number of [`Weak`] pointers to this allocation.
    ///
    /// # Examples
    ///
    /// ```
    /// use ptr_eq::rc::Rc;
    /// use ptr_eq::PtrEq;
    /// 
    /// #[derive(PtrEq, Debug)]
    /// struct Test(i64);
    /// 
    /// let five = Rc::new(Test(5));
    /// let _weak_five = Rc::downgrade(&five);
    ///
    /// assert_eq!(1, Rc::weak_count(&five));
    /// ```
    #[inline]
    pub fn weak_count(this: &Self) -> usize {
        StdRc::weak_count(&this.0)
    }

    /// Gets the number of strong (`Rc`) pointers to this allocation.
    ///
    /// # Examples
    ///
    /// ```
    /// use ptr_eq::rc::Rc;
    /// use ptr_eq::PtrEq;
    /// 
    /// #[derive(PtrEq, Debug)]
    /// struct Test(i64);
    /// 
    /// let five = Rc::new(Test(5));
    /// let _also_five = Rc::clone(&five);
    ///
    /// assert_eq!(2, Rc::strong_count(&five));
    /// ```
    #[inline]
    pub fn strong_count(this: &Self) -> usize {
        StdRc::strong_count(&this.0)
    }

    /// Returns a mutable reference into the given `Rc`, if there are
    /// no other `Rc` or [`Weak`] pointers to the same allocation.
    ///
    /// Returns [`None`] otherwise, because it is not safe to
    /// mutate a shared value.
    ///
    /// See also [`make_mut`][make_mut], which will [`clone`][clone]
    /// the inner value when there are other pointers.
    ///
    /// [make_mut]: Rc::make_mut
    /// [clone]: Clone::clone
    ///
    /// # Examples
    ///
    /// ```
    /// use ptr_eq::rc::Rc;
    /// use ptr_eq::PtrEq;
    /// 
    /// #[derive(PtrEq, Debug)]
    /// struct Test(i64);
    /// 
    /// let mut x = Rc::new(Test(3));
    /// *Rc::get_mut(&mut x).unwrap() = Test(4);
    /// assert_eq!(x.0, 4);
    ///
    /// let _y = Rc::clone(&x);
    /// assert!(Rc::get_mut(&mut x).is_none());
    /// ```
    #[inline]
    pub fn get_mut(this: &mut Self) -> Option<&mut T> {
        StdRc::get_mut(&mut this.0)
    }
}

impl<T: PtrEq + Clone> Rc<T> {
    /// Makes a mutable reference into the given `Rc`.
    ///
    /// If there are other `Rc` pointers to the same allocation, then `make_mut` will
    /// [`clone`] the inner value to a new allocation to ensure unique ownership.  This is also
    /// referred to as clone-on-write.
    ///
    /// If there are no other `Rc` pointers to this allocation, then [`Weak`]
    /// pointers to this allocation will be disassociated.
    ///
    /// See also [`get_mut`], which will fail rather than cloning.
    ///
    /// [`clone`]: Clone::clone
    /// [`get_mut`]: Rc::get_mut
    ///
    /// # Examples
    ///
    /// ```
    /// use ptr_eq::rc::Rc;
    /// use ptr_eq::PtrEq;
    /// 
    /// #[derive(PtrEq, Debug, Clone)]
    /// struct Test(i64);
    ///
    /// let mut data = Rc::new(Test(5));
    ///
    /// Rc::make_mut(&mut data).0 += 1;         // Won't clone anything
    /// let mut other_data = Rc::clone(&data);  // Won't clone inner data
    /// Rc::make_mut(&mut data).0 += 1;         // Clones inner data
    /// Rc::make_mut(&mut data).0 += 1;         // Won't clone anything
    /// Rc::make_mut(&mut other_data).0 *= 2;   // Won't clone anything
    ///
    /// // Now `data` and `other_data` point to different allocations.
    /// assert_eq!(data.0, 8);
    /// assert_eq!(other_data.0, 12);
    /// ```
    ///
    /// [`Weak`] pointers will be disassociated:
    ///
    /// ```
    /// use ptr_eq::rc::Rc;
    /// use ptr_eq::PtrEq;
    /// 
    /// #[derive(PtrEq, Debug, Clone)]
    /// struct Test(i64);
    ///
    /// let mut data = Rc::new(Test(75));
    /// let weak = Rc::downgrade(&data);
    ///
    /// assert!(75 == data.0);
    /// assert!(75 == weak.upgrade().unwrap().0);
    ///
    /// Rc::make_mut(&mut data).0 += 1;
    ///
    /// assert!(76 == data.0);
    /// assert!(weak.upgrade().is_none());
    /// ```
    #[inline]
    pub fn make_mut(this: &mut Self) -> &mut T {
        StdRc::make_mut(&mut this.0)
    }
}

impl<T: PtrEq + ?Sized> AsRef<T> for Rc<T> {
    #[inline]
    fn as_ref(&self) -> &T {
        &*(*self).0
    }
}

impl<T: PtrEq + ?Sized> Borrow<T> for Rc<T> {
    #[inline]
    fn borrow(&self) -> &T {
        &*(*self).0
    }
}

impl<T: PtrEq + ?Sized> Clone for Rc<T> {
    /// Makes a clone of the `Rc` pointer.
    ///
    /// This creates another pointer to the same allocation, increasing the
    /// strong reference count.
    ///
    /// # Examples
    ///
    /// ```
    /// use ptr_eq::rc::Rc;
    /// use ptr_eq::PtrEq;
    /// 
    /// #[derive(PtrEq)]
    /// struct Test(i64);
    ///
    /// let five = Rc::new(Test(5));
    ///
    /// let _ = Rc::clone(&five);
    /// ```
    #[inline]
    fn clone(&self) -> Rc<T> {
        Rc(StdRc::clone(&self.0))
    }
}

impl<T: PtrEq + Default> Default for Rc<T> {
    /// Creates a new `Rc<T>`, with the `Default` value for `T`.
    ///
    /// # Examples
    ///
    /// ```
    /// use ptr_eq::rc::Rc;
    /// use ptr_eq::PtrEq;
    /// 
    /// #[derive(PtrEq, Default)]
    /// struct Test(i64);
    ///
    /// let x: Rc<Test> = Default::default();
    /// assert_eq!(x.0, 0);
    /// ```
    #[inline]
    fn default() -> Rc<T> {
        Rc(StdRc::default())
    }
}

impl<T: PtrEq + ?Sized> Deref for Rc<T> {
    type Target = T;
    
    #[inline(always)]
    fn deref(&self) -> &T {
        StdRc::deref(&self.0)
    }
}

impl<T: PtrEq> From<T> for Rc<T> {
    #[inline]
    fn from(t: T) -> Self {
        Rc::new(t)
    }
}

impl<T> From<Vec<T>> for Rc<[T]>
where
    [T]: PtrEq,
{
    #[inline]
    fn from(v: Vec<T>) -> Rc<[T]> {
        Rc(StdRc::from(v))
    }
}

impl<T> iter::FromIterator<T> for Rc<[T]>
where
    [T]: PtrEq,
{
    #[inline]
    fn from_iter<I: iter::IntoIterator<Item = T>>(iter: I) -> Rc<[T]> {
        Rc(StdRc::from_iter(iter))
    }
}

impl<T: PtrEq + ?Sized> fmt::Pointer for Rc<T> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        StdRc::fmt(&self.0, f)
    }
}

/// `Weak` is a version of [`Rc`] that holds a non-owning reference to the
/// managed allocation. The allocation is accessed by calling [`upgrade`] on the `Weak`
/// pointer, which returns an [`Option`]`<`[`Rc`]`<T>>`.
///
/// Since a `Weak` reference does not count towards ownership, it will not
/// prevent the value stored in the allocation from being dropped, and `Weak` itself makes no
/// guarantees about the value still being present. Thus it may return [`None`]
/// when [`upgrade`]d. Note however that a `Weak` reference *does* prevent the allocation
/// itself (the backing store) from being deallocated.
///
/// A `Weak` pointer is useful for keeping a temporary reference to the allocation
/// managed by [`Rc`] without preventing its inner value from being dropped. It is also used to
/// prevent circular references between [`Rc`] pointers, since mutual owning references
/// would never allow either [`Rc`] to be dropped. For example, a tree could
/// have strong [`Rc`] pointers from parent nodes to children, and `Weak`
/// pointers from children back to their parents.
///
/// The typical way to obtain a `Weak` pointer is to call [`Rc::downgrade`].
///
/// [`upgrade`]: Weak::upgrade
#[repr(transparent)]
#[derive(Debug)]
pub struct Weak<T: PtrEq + ?Sized>(StdWeak<T>);

impl<T: PtrEq> Weak<T> {
    /// Constructs a new `Weak<T>`, without allocating any memory.
    /// Calling [`upgrade`] on the return value always gives [`None`].
    ///
    /// [`upgrade`]: Weak::upgrade
    ///
    /// # Examples
    ///
    /// ```
    /// use ptr_eq::rc::Weak;
    /// use ptr_eq::PtrEq;
    /// 
    /// #[derive(PtrEq)]
    /// struct Test(i64);
    ///
    /// let empty: Weak<Test> = Weak::new();
    /// assert!(empty.upgrade().is_none());
    /// ```
    #[inline]
    pub fn new() -> Weak<T> {
        Weak(StdWeak::new())
    }
}

impl<T: PtrEq + ?Sized> Weak<T> {
    /// Returns a raw pointer to the object `T` pointed to by this `Weak<T>`.
    ///
    /// The pointer is valid only if there are some strong references. The pointer may be dangling,
    /// unaligned or even [`null`] otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use ptr_eq::rc::Rc;
    /// use ptr_eq::PtrEq;
    /// use std::ptr;
    /// 
    /// #[derive(PtrEq)]
    /// struct Test(i64);
    /// 
    /// let strong = Rc::new(Test(42));
    /// let weak = Rc::downgrade(&strong);
    /// // Both point to the same object
    /// assert!(ptr::eq(&*strong, weak.as_ptr()));
    /// // The strong here keeps it alive, so we can still access the object.
    /// assert_eq!(42, unsafe { &*weak.as_ptr() }.0);
    ///
    /// drop(strong);
    /// // But not any more. We can do weak.as_ptr(), but accessing the pointer would lead to
    /// // undefined behaviour.
    /// // assert_eq!(42, unsafe { &*weak.as_ptr() }.0);
    /// ```
    ///
    /// [`null`]: core::ptr::null
    #[inline]
    pub fn as_ptr(&self) -> *const T {
        self.0.as_ptr()
    }

    /// Consumes the `Weak<T>` and turns it into a raw pointer.
    ///
    /// This converts the weak pointer into a raw pointer, while still preserving the ownership of
    /// one weak reference (the weak count is not modified by this operation). It can be turned
    /// back into the `Weak<T>` with [`from_raw`].
    ///
    /// The same restrictions of accessing the target of the pointer as with
    /// [`as_ptr`] apply.
    ///
    /// # Examples
    ///
    /// ```
    /// use ptr_eq::rc::{Rc, Weak};
    /// use ptr_eq::PtrEq;
    /// use std::ptr;
    /// 
    /// #[derive(PtrEq)]
    /// struct Test(i64);
    /// 
    /// let strong = Rc::new(Test(42));
    /// let weak = Rc::downgrade(&strong);
    /// let raw = weak.into_raw();
    ///
    /// assert_eq!(1, Rc::weak_count(&strong));
    /// assert_eq!(42, unsafe { &*raw }.0);
    ///
    /// drop(unsafe { Weak::from_raw(raw) });
    /// assert_eq!(0, Rc::weak_count(&strong));
    /// ```
    ///
    /// [`from_raw`]: Weak::from_raw
    /// [`as_ptr`]: Weak::as_ptr
    #[inline]
    pub fn into_raw(self) -> *const T {
        self.0.into_raw()
    }

    /// Converts a raw pointer previously created by [`into_raw`] back into `Weak<T>`.
    ///
    /// This can be used to safely get a strong reference (by calling [`upgrade`]
    /// later) or to deallocate the weak count by dropping the `Weak<T>`.
    ///
    /// It takes ownership of one weak reference (with the exception of pointers created by [`new`],
    /// as these don't own anything; the method still works on them).
    ///
    /// # Safety
    ///
    /// The pointer must have originated from the [`into_raw`] and must still own its potential
    /// weak reference.
    ///
    /// It is allowed for the strong count to be 0 at the time of calling this. Nevertheless, this
    /// takes ownership of one weak reference currently represented as a raw pointer (the weak
    /// count is not modified by this operation) and therefore it must be paired with a previous
    /// call to [`into_raw`].
    ///
    /// # Examples
    ///
    /// ```
    /// use ptr_eq::rc::{Rc, Weak};
    /// use ptr_eq::PtrEq;
    /// 
    /// #[derive(PtrEq)]
    /// struct Test(i64);
    ///
    /// let strong = Rc::new(Test(42));
    ///
    /// let raw_1 = Rc::downgrade(&strong).into_raw();
    /// let raw_2 = Rc::downgrade(&strong).into_raw();
    ///
    /// assert_eq!(2, Rc::weak_count(&strong));
    ///
    /// assert_eq!(42, unsafe { Weak::from_raw(raw_1) }.upgrade().unwrap().0);
    /// assert_eq!(1, Rc::weak_count(&strong));
    ///
    /// drop(strong);
    ///
    /// // Decrement the last weak count.
    /// assert!(unsafe { Weak::from_raw(raw_2) }.upgrade().is_none());
    /// ```
    ///
    /// [`into_raw`]: Weak::into_raw
    /// [`upgrade`]: Weak::upgrade
    /// [`new`]: Weak::new
    #[inline]
    pub unsafe fn from_raw(ptr: *const T) -> Weak<T> {
        Weak(StdWeak::from_raw(ptr))
    }

    /// Attempts to upgrade the `Weak` pointer to an [`Rc`], delaying
    /// dropping of the inner value if successful.
    ///
    /// Returns [`None`] if the inner value has since been dropped.
    ///
    /// # Examples
    ///
    /// ```
    /// use ptr_eq::rc::{Rc, Weak};
    /// use ptr_eq::PtrEq;
    /// 
    /// #[derive(PtrEq)]
    /// struct Test(i64);
    ///
    /// let five = Rc::new(Test(5));
    ///
    /// let weak_five = Rc::downgrade(&five);
    ///
    /// let strong_five: Option<Rc<_>> = weak_five.upgrade();
    /// assert!(strong_five.is_some());
    ///
    /// // Destroy all strong pointers.
    /// drop(strong_five);
    /// drop(five);
    ///
    /// assert!(weak_five.upgrade().is_none());
    /// ```
    #[inline]
    pub fn upgrade(&self) -> Option<Rc<T>> {
        if let Some(rc) = self.0.upgrade() {
            Some(Rc(rc))
        } else {
            None
        }
    }

    /// Gets the number of `Weak` pointers pointing to this allocation.
    ///
    /// If no strong pointers remain, this will return zero.
    #[inline]
    pub fn weak_count(this: &Self) -> usize {
        this.0.weak_count()
    }

    /// Gets the number of strong (`Rc`) pointers pointing to this allocation.
    ///
    /// If `self` was created using [`Weak::new`], this will return 0.
    #[inline]
    pub fn strong_count(this: &Self) -> usize {
        this.0.strong_count()
    }
}

impl<T: PtrEq + ?Sized> Clone for Weak<T> {
    /// Makes a clone of the `Weak` pointer that points to the same allocation.
    ///
    /// # Examples
    ///
    /// ```
    /// use ptr_eq::rc::{Rc, Weak};
    /// use ptr_eq::PtrEq;
    /// 
    /// #[derive(PtrEq)]
    /// struct Test(i64);
    ///
    /// let weak_five = Rc::downgrade(&Rc::new(Test(5)));
    ///
    /// let _ = Weak::clone(&weak_five);
    /// ```
    #[inline]
    fn clone(&self) -> Weak<T> {
        Weak(self.0.clone())
    }
}

impl<T: PtrEq> Default for Weak<T> {
    /// Constructs a new `Weak<T>`, allocating memory for `T` without initializing
    /// it. Calling [`upgrade`] on the return value always gives [`None`].
    ///
    /// [`None`]: Option
    /// [`upgrade`]: Weak::upgrade
    ///
    /// # Examples
    ///
    /// ```
    /// use ptr_eq::rc::Weak;
    /// use ptr_eq::PtrEq;
    /// 
    /// #[derive(PtrEq)]
    /// struct Test(i64);
    /// 
    /// let empty: Weak<Test> = Default::default();
    /// assert!(empty.upgrade().is_none());
    /// ```
    #[inline]
    fn default() -> Weak<T> {
        Weak(StdWeak::default())
    }
}