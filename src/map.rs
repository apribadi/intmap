use crate::prelude::*;

pub struct HashMapNZ64<A> {
  table: *const Slot<A>, // covariant in `A`
  mults: [u64; 2],
  shift: u8,
  extra: u8,
  space: usize,
  table_last_slot: *const Slot<A>,
}

unsafe impl<A : Send> Send for HashMapNZ64<A> {}

unsafe impl<A : Sync> Sync for HashMapNZ64<A> {}

struct Slot<A> {
  hash: u64,
  value: MaybeUninit<A>,
}

const INITIAL_SHIFT: u8 = 61;
const INITIAL_EXTRA: u8 = 0;
const INITIAL_NUM_SLOTS: usize = num_slots(INITIAL_SHIFT, INITIAL_EXTRA);

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
  let s = shift as usize;
  let e = extra as usize;
  let w = 64 - s;

  (1 << w) + ((w + 1) << e)
}

impl<A> HashMapNZ64<A> {
  pub fn new() -> Self {
    Self {
      mults: Rng::with_thread_local(|g| [g.u64() | 1, g.u64() | 1]),
      table: ptr::null(),
      space: 0,
      shift: INITIAL_SHIFT,
      extra: INITIAL_EXTRA,
      table_last_slot: ptr::null(),
    }
  }

  #[inline]
  pub fn len(&self) -> usize {
    (1 << (64 - self.shift - 1)) - self.space
  }

  #[inline]
  pub fn is_empty(&self) -> bool {
    self.len() == 0
  }

  #[inline]
  pub fn contains_key(&self, key: NonZeroU64) -> bool {
    let t = self.table;

    if t.is_null() { return false; }

    let m = self.mults;
    let s = self.shift;
    let h = hash(m, key);
    let i = (! h >> s) as usize;

    let mut p = unsafe { t.add(i) };
    let mut x = unsafe { &*p }.hash;

    while x > h {
      p = unsafe { p.add(1) };
      x = unsafe { &*p }.hash;
    }

    return x == h;
  }

  #[inline]
  pub fn get(&self, key: NonZeroU64) -> Option<&A> {
    let t = self.table;

    if t.is_null() { return None; }

    let m = self.mults;
    let s = self.shift;
    let h = hash(m, key);
    let i = (! h >> s) as usize;

    let mut p = unsafe { t.add(i) };
    let mut x = unsafe { &*p }.hash;

    while x > h {
      p = unsafe { p.add(1) };
      x = unsafe { &*p }.hash;
    }

    if x == h {
      Some(unsafe { (&*p).value.assume_init_ref() })
    } else {
      None
    }
  }

  #[inline]
  pub fn get_mut(&mut self, key: NonZeroU64) -> Option<&mut A> {
    let t = self.table as *mut Slot<A>;

    if t.is_null() { return None; }

    let m = self.mults;
    let s = self.shift;
    let h = hash(m, key);
    let i = (! h >> s) as usize;

    let mut p = unsafe { t.add(i) };
    let mut x = unsafe { &*p }.hash;

    while x > h {
      p = unsafe { p.add(1) };
      x = unsafe { &*p }.hash;
    }

    if x == h {
      Some(unsafe { (&mut *p).value.assume_init_mut() })
    } else {
      None
    }
  }

  #[inline]
  pub fn insert(&mut self, key: NonZeroU64, value: A) -> Option<A> {
    let t = self.table as *mut Slot<A>;

    if t.is_null() { return self.insert_cold_null_table(key, value); }

    let m = self.mults;
    let s = self.shift;
    let h = hash(m, key);
    let i = (! h >> s) as usize;

    let mut p = unsafe { t.add(i) };
    let mut x = unsafe { &*p }.hash;

    while x > h {
      p = unsafe { p.add(1) };
      x = unsafe { &*p }.hash;
    }

    if x == h {
      Some(mem::replace(unsafe { (&mut *p).value.assume_init_mut() }, value))
    } else {
      unsafe { &mut *p }.hash = h;
      let mut a = Slot { hash: x, value: mem::replace(&mut unsafe { &mut *p }.value, MaybeUninit::new(value)) };

      while a.hash != 0 {
        p = unsafe { p.add(1) };
        a = unsafe { p.replace(a) };
      }

      let k = self.space - 1;
      self.space = k;
      let q = self.table_last_slot;

      if k == 0 || ptr::eq(p, q) { return self.insert_cold_grow_table(); }

      None
    }
  }

  #[inline(never)]
  #[cold]
  fn insert_cold_null_table(&mut self, key: NonZeroU64, value: A) -> Option<A> {
    // PRECONDITION:
    //
    // - The hashmap is unchanged since its creation by `new`.

    // The following asserts a constant expression!  Note that `size_of()`
    // includes alignment padding.

    assert!(INITIAL_NUM_SLOTS <= isize::MAX as usize / mem::size_of::<Slot<A>>());

    let align = mem::align_of::<Slot<A>>();
    let size = INITIAL_NUM_SLOTS * mem::size_of::<Slot<A>>();

    // SAFETY:
    //
    // - Because `align` is the alignment of `Slot<A>` we know that it is a
    //   valid alignment.
    // - We've previously asserted that the length is not too long.

    let layout = unsafe { Layout::from_size_align_unchecked(size, align) };

    // SAFETY:
    //
    // - `size` is positive.

    // Note that `alloc_zeroed` initializes all slot hash values to zero.

    let t = unsafe { std::alloc::alloc_zeroed(layout) } as *mut Slot<A>;

    if t.is_null() { match std::alloc::handle_alloc_error(layout) {} }

    // Inserts into a fresh table. We know that this won't collide!

    let m = self.mults;
    let h = hash(m, key);
    let i = (! h >> INITIAL_SHIFT) as usize;
    let p = unsafe { t.add(i) };
    let q = unsafe { t.add(INITIAL_NUM_SLOTS - 1) };

    unsafe { &mut *p }.hash = h;
    unsafe { &mut *p }.value = MaybeUninit::new(value);

    self.table = t;
    self.space = 1 << (64 - INITIAL_SHIFT - 1);
    self.table_last_slot = q;

    None
  }

  #[inline(never)]
  #[cold]
  fn insert_cold_grow_table(&mut self) -> Option<A> {
    let t = self.table;
    let q = self.table_last_slot;
    let mut k = self.space;
    let mut s = self.shift;
    let mut e = self.extra;

    if k == 0 {
      k = 1 << (64 - s - 1);
      s = s - 1;
    }

    if unsafe { &*q }.hash != 0 {
      e = e + 1;
    }

    let n = num_slots(s, e); // TODO: overflow checking

    let _ = t;
    let _ = n;

    self.space = k;
    self.shift = s;
    self.extra = e;

    // TODO

    unimplemented!()
  }


  #[inline]
  pub fn remove(&mut self, key: NonZeroU64) -> Option<A> {
    let t = self.table as *mut Slot<A>;

    if t.is_null() { return None; }

    let m = self.mults;
    let s = self.shift;
    let h = hash(m, key);
    let i = (! h >> s) as usize;

    let mut p = unsafe { t.add(i) };
    let mut x = unsafe { &*p }.hash;

    while x > h {
      p = unsafe { p.add(1) };
      x = unsafe { &*p }.hash;
    }

    if x == h {
      let v = unsafe { (&mut *p).value.assume_init_read() };

      loop {
        let q = unsafe { p.add(1) };
        let a = unsafe { q.read() };
        if true || a.hash == 0 { break; } // TODO
        unsafe { p.write(a) };
        p = q;
      }

      unsafe { &mut *p }.hash = 0;
      self.space = self.space + 1;
      Some(v)
    } else {
      None
    }
  }

  pub fn clear(&mut self) {
    let t = self.table as *mut Slot<A>;

    if t.is_null() { return; }

    let s = self.shift;
    let e = self.extra;
    let n = num_slots(s, e);

    for p in (0 .. n).map(|i| unsafe { t.add(i) }) {
      if mem::needs_drop::<A>() && unsafe { &*p }.hash != 0 {
        unsafe { (&mut *p).value.assume_init_drop() };
      }

      unsafe { &mut *p }.hash = 0;
    }
  }
}

impl<A> Drop for HashMapNZ64<A> {
  fn drop(&mut self) {
    let t = self.table as *mut Slot<A>;

    if t.is_null() { return; }

    let s = self.shift;
    let e = self.extra;
    let n = num_slots(s, e);

    if mem::needs_drop::<A>() {
      for p in (0 .. n).map(|i| unsafe { t.add(i) }) {
        if unsafe { &*p }.hash != 0 {
          unsafe { (&mut *p).value.assume_init_drop() };
        }
      }
    }

    let align = mem::align_of::<Slot<A>>();
    let size = n * mem::size_of::<Slot<A>>();
    let layout = unsafe { Layout::from_size_align_unchecked(size, align) };

    unsafe { std::alloc::dealloc(t as *mut u8, layout) };
  }
}
