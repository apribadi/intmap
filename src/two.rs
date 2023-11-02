use core::mem::MaybeUninit;
use core::num::NonZeroU64;
use crate::ptr::Ptr;

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
  __var: core::marker::PhantomData<T>,
}

// NB: We need `repr(C)` so that we're guaranteed that the hash is at the front
// of the struct.

#[repr(C)]
struct Slot<T> {
  hash: u64,
  data: MaybeUninit<T>,
}

#[inline(always)]
fn spot(h: u64, s: usize) -> isize {
  (h >> 1).wrapping_shr(s as u32) as isize
}

impl<T> HashMapNZ64<T> {
  pub fn get(&self, key: NonZeroU64) -> Option<&T> {
    let m = self.seeds;
    let h = hash(m, key).get();
    let t = self.table;
    let s = self.shift;
    let i = spot(h, s);

    let mut p = t.gep::<Slot<T>>(- i);
    let mut x;

    loop {
      x = unsafe { p.read::<u64>() };
      if x <= h { break; }
      p = p.gep::<Slot<T>>(1);
    }

    if x != h {
      return None;
    }

    Some(unsafe { p.as_ref::<Slot<T>>().data.assume_init_ref() })
  }

  pub fn contains_key(&self, key: NonZeroU64) -> bool {
    let m = self.seeds;
    let h = hash(m, key).get();
    let t = self.table;
    let s = self.shift;
    let i = spot(h, s);

    let mut p = t.gep::<Slot<T>>(- i);
    let mut x;

    loop {
      x = unsafe { p.read::<u64>() };
      if x <= h { break; }
      p = p.gep::<Slot<T>>(1);
    }

    x == h
  }
}

/*
pub fn contains_key(t: &HashMapNZ64<u64>, k: NonZeroU64) -> bool {
  t.contains_key(k)
}
*/

pub fn contains_key2(t: &HashMapNZ64<u64>, k: NonZeroU64) -> bool {
  t.get(k).is_some()
}

pub fn get(t: &HashMapNZ64<u64>, k: NonZeroU64) -> Option<&u64> {
  t.get(k)
}

pub fn get_value(t: &HashMapNZ64<u64>, k: NonZeroU64) -> Option<u64> {
  match t.get(k) {
    None => { None }
    Some(&r) => { Some(r) }
  }
}

pub fn twice(t: &HashMapNZ64<u64>, x: NonZeroU64, y: NonZeroU64) -> u64 {
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
