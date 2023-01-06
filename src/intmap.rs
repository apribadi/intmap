use crate::prelude::*;

pub struct IntMap<A> {
  table: *mut Slot<A>,
  mults: [u64; 2],
  shift: u8,
  count: usize,
}

struct Slot<A> {
  hash: u64,
  value: MaybeUninit<A>,
}

impl<A> IntMap<A> {
  pub fn new() -> Self {
    Self {
      mults: THREAD_LOCAL_RNG.with(|rng| rng.u64x2()),
      table: ptr::null_mut(),
      count: 0,
      shift: 0,
    }
  }

  #[inline(always)]
  fn hash(&self, x: NonZeroU64) -> u64 {
    let a = self.mults[0];
    let b = self.mults[1];
    let x = u64::from(x);
    let x = x.wrapping_mul(a);
    let x = x.swap_bytes();
    let x = x.wrapping_mul(b);
    x
  }

  #[inline]
  pub fn is_empty(&self) -> bool {
    self.count == 0
  }

  #[inline]
  pub fn contains_key(&self, key: NonZeroU64) -> bool {
    let t = self.table;

    if t.is_null() { return false; }

    let x = self.hash(key);
    let k = self.shift;
    let i = ! x >> k;

    let mut p = t.wrapping_add(i as usize);

    loop {
      let s = unsafe { &*p };
      let y = s.hash;

      if y <= x { return y == x; }

      p = p.wrapping_add(1);
    }
  }

  #[inline]
  pub fn get(&self, key: NonZeroU64) -> Option<&A> {
    let t = self.table;

    if t.is_null() { return None; }

    let x = self.hash(key);
    let k = self.shift;
    let i = ! x >> k;

    let mut p = t.wrapping_add(i as usize);

    loop {
      let s = unsafe { &*p };
      let y = s.hash;

      if y <= x {
        if y != x { return None; }

        let v = &s.value;
        let v = unsafe { v.assume_init_ref() };

        return Some(v);
      }

      p = p.wrapping_add(1);
    }
  }

  #[inline]
  pub fn get_mut(&mut self, key: NonZeroU64) -> Option<&mut A> {
    unimplemented!()
  }

  #[inline]
  pub fn insert(&mut self, key: NonZeroU64, value: A) -> Option<A> {
    unimplemented!()
  }

  #[inline]
  pub fn remove(&mut self, key: NonZeroU64) -> Option<A> {
    unimplemented!()
  }

  pub fn clear(&mut self) {
    unimplemented!()
  }
}

impl<A> Drop for IntMap<A> {
  fn drop(&mut self) {
    // TODO
  }
}

pub fn foo(t: &IntMap<u64>) -> bool {
  t.contains_key(unsafe { NonZeroU64::new_unchecked(13) })
}

pub fn bar(t: &IntMap<u64>) -> Option<&u64> {
  t.get(unsafe { NonZeroU64::new_unchecked(13) })
}
