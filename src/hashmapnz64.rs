use crate::prelude::*;

pub struct HashMapNZ64<A> {
  table: *const Slot<A>, // covariant in `A`
  mults: [u64; 2],
  shift: u8,
  count: usize,
}

struct Slot<A> {
  hash: u64,
  value: MaybeUninit<A>,
}

#[inline(always)]
fn hash(m: [u64; 2], x: NonZeroU64) -> u64 {
  let a = m[0]; // `m`s should be odd
  let b = m[1];
  let x = u64::from(x);
  let x = x.wrapping_mul(a);
  let x = x.swap_bytes();
  let x = x.wrapping_mul(b);
  x
}

impl<A> HashMapNZ64<A> {
  pub fn new() -> Self {
    Self {
      mults: Rng::with_thread_local(|g| [g.u64() | 1, g.u64() | 1]),
      table: ptr::null(),
      shift: 0,
      count: 0,
    }
  }

  #[inline]
  pub fn is_empty(&self) -> bool {
    self.count == 0
  }

  #[inline]
  pub fn contains_key(&self, key: NonZeroU64) -> bool {
    let t = self.table;

    if t.is_null() { return false; }

    let m = self.mults;
    let k = self.shift;
    let x = hash(m, key);
    let i = (! x >> k) as usize;

    let mut p = t.wrapping_add(i);

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

    let m = self.mults;
    let k = self.shift;
    let x = hash(m, key);
    let i = (! x >> k) as usize;

    let mut p = t.wrapping_add(i);

    loop {
      let s = unsafe { &*p };
      let y = s.hash;

      if y <= x {
        if y == x {
          return None;
        } else {
          let v = &s.value;
          let v = unsafe { v.assume_init_ref() };
          return Some(v);
        }
      }

      p = p.wrapping_add(1);
    }
  }

  #[inline]
  pub fn get_mut(&mut self, key: NonZeroU64) -> Option<&mut A> {
    let t = self.table as *mut Slot<A>;

    if t.is_null() { return None; }

    let m = self.mults;
    let k = self.shift;
    let x = hash(m, key);
    let i = (! x >> k) as usize;

    let mut p = t.wrapping_add(i);

    loop {
      let s = unsafe { &mut *p };
      let y = s.hash;

      if y <= x {
        if y == x {
          return None;
        } else {
          let v = &mut s.value;
          let v = unsafe { v.assume_init_mut() };
          return Some(v);
        }
      }

      p = p.wrapping_add(1);
    }
  }

  #[inline]
  pub fn insert(&mut self, key: NonZeroU64, value: A) -> Option<A> {
    let t = self.table as *mut Slot<A>;

    if t.is_null() { return None; }

    let m = self.mults;
    let k = self.shift;
    let x = hash(m, key);
    let i = (! x >> k) as usize;

    let mut p = t.wrapping_add(i);

    loop {
      let s = unsafe { &mut *p };
      let y = s.hash;

      if y <= x {
        if y == x {
          let v = &mut s.value;
          let v = unsafe { v.assume_init_mut() };
          let v = mem::replace(v, value);

          return Some(v);
        } else {
          // TODO: finish insert.

          // TODO: maybe grow.

          return None;
        }
      }

      p = p.wrapping_add(1);
    }
  }

  #[inline]
  pub fn remove(&mut self, key: NonZeroU64) -> Option<A> {
    let t = self.table as *mut Slot<A>;

    if t.is_null() { return None; }

    let m = self.mults;
    let k = self.shift;
    let x = hash(m, key);
    let i = (! x >> k) as usize;

    let mut p = t.wrapping_add(i);

    loop {
      let s = unsafe { &mut *p };
      let y = s.hash;

      if y <= x {
        if y == x {
          // TODO

          unimplemented!()
        } else {
          return None;
        }
      }

      p = p.wrapping_add(1);
    }
  }

  pub fn clear(&mut self) {
    unimplemented!()
  }

  fn num_slots(&self) -> usize {
    let k = self.shift;
    (1 << k) + (k as usize) + 1
  }
}

impl<A> Drop for HashMapNZ64<A> {
  fn drop(&mut self) {
    let t = self.table as *mut Slot<A>;

    if ! t.is_null() {
      let num_slots = self.num_slots();

      for i in 0 .. num_slots {
        let p = t.wrapping_add(i);
        let s = unsafe { &mut *p };
        if s.hash != 0 { unsafe { s.value.assume_init_drop() } }
      }

      let size = mem::size_of::<Slot<A>>() * num_slots;
      let align = mem::align_of::<Slot<A>>();
      let layout = unsafe { Layout::from_size_align_unchecked(size, align) };
      unsafe { std::alloc::dealloc(t as *mut u8, layout) };
    }
  }
}

pub fn foo(t: &HashMapNZ64<u64>) -> bool {
  t.contains_key(unsafe { NonZeroU64::new_unchecked(13) })
}

pub fn bar(t: &HashMapNZ64<u64>) -> Option<&u64> {
  t.get(unsafe { NonZeroU64::new_unchecked(13) })
}
