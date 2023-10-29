use core::mem::MaybeUninit;
use core::num::NonZeroU64;
use crate::ptr::Ptr;

#[inline(always)]
unsafe fn assume(p: bool) {
  if ! p { unsafe { core::hint::unreachable_unchecked() } }
}

#[derive(Clone, Copy)]
struct Seeds(u64, u64);

#[inline(always)]
const fn hash(Seeds(a, b): Seeds, x: NonZeroU64) -> NonZeroU64 {
  let x = x.get();
  let x = x.wrapping_mul(a);
  let x = x.swap_bytes();
  let x = x.wrapping_mul(b);
  unsafe { NonZeroU64::new_unchecked(x) }
}

pub struct HashMapNZ64<T> {
  seeds: Seeds,
  table: Ptr,
  shift: usize,
  space: isize,
  _mark: core::marker::PhantomData<T>,
}

impl<T> HashMapNZ64<T> {
  pub fn get(&self, key: NonZeroU64) -> Option<&T> {
    let m = self.seeds;
    let h = hash(m, key).get();
    let t = self.table;
    let s = self.shift;
    unsafe { assume(s <= 63) };
    let mut i = (! h >> s) as isize;
    let mut x;

    loop {
      x = unsafe { t.gep::<u64>(i).read::<u64>() };
      if x <= h { break; }
      i = i + 1;
    }

    if x != h {
      return None;
    }

    Some(unsafe { t.gep::<T>(- i - 1).as_ref() })
  }

  /*
  pub fn contains_key(&self, key: NonZeroU64) -> bool {
    let a = self.a;
    let b = self.b;
    let h = key.get();
    let h = h.wrapping_mul(a);
    let h = h.swap_bytes();
    let h = h.wrapping_mul(b);
    let s = self.s;
    let t = self.t;
    unsafe { assume(s <= 63) };
    let mut i = (h >> s) as usize;
    let mut x;

    loop {
      x = unsafe { t.cast::<u64>().add(i).read() };
      i = i + 1;
      if x >= h { break; }
    }

    x == h
  }
  */
}

/*
pub fn contains_key(t: &HashMapNZ64<()>, k: NonZeroU64) -> bool {
  t.contains_key(k)
}
*/

pub fn get(t: &HashMapNZ64<u32>, k: NonZeroU64) -> Option<&u32> {
  t.get(k)
}

/*
pub fn twice(t: &HashMapNZ64<u32>, x: NonZeroU64, y: NonZeroU64) -> u32 {
  match t.get(x) {
    None => { 0 }
    Some(&a) => {
      match t.get(y) {
        None => { a }
        Some(&b) => { a + b }
      }
    }
  }
}
*/
