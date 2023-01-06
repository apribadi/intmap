use crate::prelude::*;

pub struct HashMapNZ64<A> {
  mults: [u64; 2],
  table: *const Slot<A>, // covariant in `A`
  count: usize,
  shift: u8,
  extra: u8,
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

#[inline(always)]
fn num_slots(shift: u8, extra: u8) -> usize {
  let k = shift as usize;
  let e = extra as usize;
  let w = 64 - k;

  (1 << w) + ((w + 1) << e)
}

impl<A> HashMapNZ64<A> {
  pub fn new() -> Self {
    Self {
      mults: Rng::with_thread_local(|g| [g.u64() | 1, g.u64() | 1]),
      table: ptr::null(),
      count: 0,
      shift: 61,
      extra: 0,
    }
  }

  #[inline]
  pub fn is_empty(&self) -> bool {
    self.count == 0
  }

  #[inline]
  pub fn len(&self) -> usize {
    self.count
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
    let mut y;

    loop {
      y = unsafe { &*p }.hash;
      if y <= x { break; }
      p = p.wrapping_add(1);
    }

    return y == x;
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
    let mut y;

    loop {
      y = unsafe { &*p }.hash;
      if y <= x { break; }
      p = p.wrapping_add(1);
    }

    if y == x {
      let s = unsafe { &*p };
      let v = &s.value;
      let v = unsafe { v.assume_init_ref() };
      Some(v)
    } else {
      None
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
    let mut y;

    loop {
      y = unsafe { &*p }.hash;
      if y <= x { break; }
      p = p.wrapping_add(1);
    }

    if y == x {
      let s = unsafe { &mut *p };
      let v = &mut s.value;
      let v = unsafe { v.assume_init_mut() };
      Some(v)
    } else {
      None
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
    let mut y;

    loop {
      y = unsafe { &*p }.hash;
      if y <= x { break; }
      p = p.wrapping_add(1);
    }

    if y == x {
      let s = unsafe { &mut *p };
      let v = &mut s.value;
      let v = unsafe { v.assume_init_mut() };
      let v = mem::replace(v, value);
      Some(v)
    } else {
      // TODO: finish insert.
      // TODO: maybe grow.

      // None

      unimplemented!()
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
    let mut y;

    loop {
      y = unsafe { &*p }.hash;
      if y <= x { break; }
      p = p.wrapping_add(1);
    }

    if y == x {
      // TODO

      unimplemented!()
    } else {
      None
    }
  }

  pub fn clear(&mut self) {
    let t = self.table as *mut Slot<A>;

    if t.is_null() { return; }

    let k = self.shift;
    let e = self.extra;
    let n = num_slots(k, e);

    for i in 0 .. n {
      let p = t.wrapping_add(i);
      let s = unsafe { &mut *p };
      let x = s.hash;
      let v = &mut s.value;

      if x != 0 { unsafe { v.assume_init_drop() } }

      s.hash = 0;
    }
  }
}

impl<A> Drop for HashMapNZ64<A> {
  fn drop(&mut self) {
    let t = self.table as *mut Slot<A>;

    if t.is_null() { return; }

    let k = self.shift;
    let e = self.extra;
    let n = num_slots(k, e);

    for i in 0 .. n {
      let p = t.wrapping_add(i);
      let s = unsafe { &mut *p };
      let x = s.hash;
      let v = &mut s.value;

      if x != 0 { unsafe { v.assume_init_drop() } }
    }

    let table = t as *mut u8;
    let size = mem::size_of::<Slot<A>>() * n;
    let align = mem::align_of::<Slot<A>>();
    let layout = unsafe { Layout::from_size_align_unchecked(size, align) };

    unsafe { std::alloc::dealloc(table, layout) };
  }
}
