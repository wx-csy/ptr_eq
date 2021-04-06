use core::{borrow, fmt};
use std::{any::Any, iter, ops::Deref, pin::Pin, rc::Rc as StdRc, rc::Weak as StdWeak};

#[repr(transparent)]
pub struct Rc<T: ?Sized>(StdRc<T>);

#[repr(transparent)]
pub struct Weak<T: ?Sized>(StdWeak<T>);

impl<T> Rc<T> {
    pub fn new(value: T) -> Rc<T> {
        Rc(StdRc::new(value))
    }

    pub fn pin(value: T) -> Pin<Rc<T>> {
        unsafe {
            Pin::new_unchecked(Rc::new(value))
        }
    }

    pub fn try_unwrap(this: Self) -> Result<T, Self> {
        StdRc::try_unwrap(this.0).or_else(|ret| Err(Rc(ret)))
    }
}

impl<T: ?Sized> Rc<T> {
    pub fn into_raw(this: Self) -> *const T {
        StdRc::into_raw(this.0)
    }

    pub fn as_ptr(this: &Self) -> *const T {
        StdRc::as_ptr(&this.0)
    }

    pub unsafe fn from_raw(ptr: *const T) -> Self {
        Rc(StdRc::from_raw(ptr))
    }

    pub fn downgrade(this: &Self) -> Weak<T> {
        Weak(StdRc::downgrade(&this.0))
    }

    pub fn weak_count(this: &Self) -> usize {
        StdRc::weak_count(&this.0)
    }

    pub fn strong_count(this: &Self) -> usize {
        StdRc::strong_count(&this.0)
    }

    pub fn get_mut(this: &mut Self) -> Option<&mut T> {
        StdRc::get_mut(&mut this.0)
    }
}

impl<T: Clone> Rc<T> {
    pub fn make_mut(this: &mut Self) -> &mut T {
        StdRc::make_mut(&mut this.0)
    }
}

impl Rc<dyn Any> {
    pub fn downcast<T: Any>(self) -> Result<Rc<T>, Rc<dyn Any>> {
        match StdRc::downcast::<T>(self.0) {
            Ok(p) => Ok(Rc(p)),
            Err(p) => Err(Rc(p)),
        }
    }
}

impl <T: ?Sized> AsRef<T> for Rc<T> {
    fn as_ref(&self) -> &T {
        &*(*self).0
    }
}

impl <T: ?Sized> borrow::Borrow<T> for Rc<T> {
    fn borrow(&self) -> &T {
        &*(*self).0
    }
}

impl <T: ?Sized> Clone for Rc<T> {
    fn clone(&self) -> Rc<T> {
        Rc(StdRc::clone(&self.0))
    }
}

impl<T: Default> Default for Rc<T> {
    fn default() -> Rc<T> {
        Rc(StdRc::default())
    }
}

impl <T: ?Sized> Deref for Rc<T> {
    type Target = T;

    fn deref(&self) -> &T {
        StdRc::deref(&self.0)
    }
}

impl<T> From<T> for Rc<T> {
    fn from(t: T) -> Self {
        Rc::new(t)
    }
}

impl<T> From<StdRc<T>> for Rc<T> {
    fn from(t: StdRc<T>) -> Self {
        Rc(t)
    }
}

impl<T> From<Rc<T>> for StdRc<T> {
    fn from(t: Rc<T>) -> Self {
        t.0
    }
}

impl<T> From<Vec<T>> for Rc<[T]> {
    fn from(v: Vec<T>) -> Rc<[T]> {
        Rc(StdRc::from(v))
    }
}

impl<T> iter::FromIterator<T> for Rc<[T]> {
    fn from_iter<I: iter::IntoIterator<Item = T>>(iter: I) -> Rc<[T]> {
        Rc(StdRc::from_iter(iter))
    }
}

impl<T: ?Sized> fmt::Pointer for Rc<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        StdRc::fmt(&self.0, f)
    }
}