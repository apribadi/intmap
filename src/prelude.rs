pub use core::alloc::Layout;
pub use core::array;
pub use core::cell::Cell;
pub use core::cmp::max;
pub use core::fmt;
pub use core::hint::unreachable_unchecked;
pub use core::iter::FusedIterator;
pub use core::marker::PhantomData;
pub use core::mem::MaybeUninit;
pub use core::mem;
pub use core::num::NonZeroU128;
pub use core::num::NonZeroU64;
pub use core::ops::Index;
pub use core::ops::IndexMut;
pub use core::ptr::NonNull;
pub use core::ptr;
pub use crate::map::HashMapNZ64;
pub use crate::map::Keys;
pub use crate::rng::Rng;
pub use crate::rng;

#[inline(always)]
pub fn each_mut<A, F>(mut p: *mut A, q: *const A, mut f: F) where F: FnMut(*mut A) -> () {
  loop { f(p); if ptr::eq(p, q) { break; } p = p.wrapping_add(1); }
}
