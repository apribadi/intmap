use crate::prelude::*;

const INITIAL_SHIFT: u8 = 61;
const INITIAL_EXTRA: u8 = 0;
const INITIAL_NUM_SLOTS: usize = num_slots(INITIAL_SHIFT, INITIAL_EXTRA);

pub struct HashMapNZ64<A> {
  mults: [u64; 2],
  table: *const Slot<A>, // covariant in `A`
  count: usize,
  shift: u8,
  extra: u8,
}

unsafe impl<A> Send for HashMapNZ64<A> {}
unsafe impl<A> Sync for HashMapNZ64<A> {}

struct Slot<A> {
  hash: u64,
  value: MaybeUninit<A>,
}

#[inline(always)]
const fn hash(m: [u64; 2], x: NonZeroU64) -> u64 {
  let a = m[0]; // `m`s should be odd
  let b = m[1];
  let x = x.get();
  let x = x.wrapping_mul(a);
  let x = x.swap_bytes();
  let x = x.wrapping_mul(b);
  x
}

#[inline(always)]
const fn num_slots(shift: u8, extra: u8) -> usize {
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
      shift: INITIAL_SHIFT,
      extra: INITIAL_EXTRA,
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
      let v = &unsafe { &*p }.value;
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
      let v = &mut unsafe { &mut *p }.value;
      let v = unsafe { v.assume_init_mut() };
      Some(v)
    } else {
      None
    }
  }

  #[inline]
  pub fn insert(&mut self, key: NonZeroU64, value: A) -> Option<A> {
    let t = self.table as *mut Slot<A>;

    if t.is_null() { return self.insert_cold_table_is_null(key, value); }

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
      let v = &mut unsafe { &mut *p }.value;
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

  #[inline(never)]
  #[cold]
  fn insert_cold_table_is_null(&mut self, key: NonZeroU64, value: A) -> Option<A> {
    // PRECONDITION:
    //
    // - The hashmap is unchanged since its creation by `new`.

    // This asserts a constant expression!
    //
    // Note that `size_of()` includes alignment padding.

    assert!(INITIAL_NUM_SLOTS <= isize::MAX as usize / mem::size_of::<Slot<A>>());

    let align = mem::align_of::<Slot<A>>();
    let size = INITIAL_NUM_SLOTS * mem::size_of::<Slot<A>>();

    // SAFETY:
    //
    // - Because `align` is the alignment of `Slot<A>` we know that it is a
    //   valid alignment.
    // - We've asserted that the length is not too long.

    let layout = unsafe { Layout::from_size_align_unchecked(size, align) };

    // SAFETY:
    //
    // - `size` is positive.

    // Note that `alloc_zeroed` initializes all slot hash values to zero.

    let table = unsafe { std::alloc::alloc_zeroed(layout) };

    if table.is_null() { match std::alloc::handle_alloc_error(layout) {} }

    // Inserts into a fresh table. We know that there won't be a collision!

    let t = table as *mut Slot<A>;
    let m = self.mults;
    let x = hash(m, key);
    let i = (! x >> INITIAL_SHIFT) as usize;
    let p = t.wrapping_add(i);
    let s = unsafe { &mut *p };

    s.hash = x;
    s.value.write(value);

    self.table = table as *const Slot<A>;
    self.count = 1;

    None
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

      s.hash = 0;

      if mem::needs_drop::<A>() && x != 0 { unsafe { v.assume_init_drop() } }
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

    if mem::needs_drop::<A>() {
      for i in 0 .. n {
        let p = t.wrapping_add(i);
        let s = unsafe { &mut *p };
        let x = s.hash;
        let v = &mut s.value;

        if x != 0 { unsafe { v.assume_init_drop() } }
      }
    }

    let align = mem::align_of::<Slot<A>>();
    let size = n * mem::size_of::<Slot<A>>();
    let layout = unsafe { Layout::from_size_align_unchecked(size, align) };

    unsafe { std::alloc::dealloc(t as *mut u8, layout) };
  }
}
