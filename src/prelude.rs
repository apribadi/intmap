pub use core::alloc::Layout;
pub use core::array;
pub use core::cell::Cell;
pub use core::cmp::max;
pub use core::fmt;
pub use core::hint;
pub use core::iter::FusedIterator;
pub use core::marker::PhantomData;
pub use core::mem::ManuallyDrop;
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
pub const unsafe fn assume(p: bool) {
  if ! p { unsafe { hint::unreachable_unchecked() } }
}

#[inline(always)]
#[cold]
pub const fn cold() {}

#[inline(always)]
pub const fn expect(p: bool, q: bool) -> bool {
  if p != q { cold() }
  p
}
