use crate::prelude::*;

pub struct HashMapNZ64<A> {
  mults: [u64; 2],
  table: *const Slot<A>, // covariant in `A`
  shift: usize,
  space: usize,
  check: *const Slot<A>,
}

unsafe impl<A : Send> Send for HashMapNZ64<A> {}
unsafe impl<A : Sync> Sync for HashMapNZ64<A> {}

struct Slot<A> {
  hash: u64,
  value: MaybeUninit<A>,
}

const INITIAL_SHIFT: usize = 61;
const INITIAL_SPACE: usize = 1 << (64 - INITIAL_SHIFT - 1);
const INITIAL_NUM_SLOTS: usize = 12;

#[inline(always)]
const fn hash(m: [u64; 2], x: NonZeroU64) -> u64 {
  let a = m[0]; // `m[_]`s should be odd
  let b = m[1];
  let x = x.get();
  let x = x.wrapping_mul(a);
  let x = x.swap_bytes();
  let x = x.wrapping_mul(b);
  x
}

#[inline(always)]
const fn spot(shift: usize, h: u64) -> isize {
  (h >> shift) as isize
}

impl<A> HashMapNZ64<A> {
  pub fn new() -> Self {
    Self {
      mults: Rng::with_thread_local(|g| [g.u64() | 1, g.u64() | 1]),
      table: ptr::null(),
      shift: INITIAL_SHIFT,
      space: INITIAL_SPACE,
      check: ptr::null(),
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
    let i = spot(s, h);

    let mut p = unsafe { t.sub(i as usize) };
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
    let i = spot(s, h);

    let mut p = unsafe { t.sub(i as usize) };
    let mut x = unsafe { &*p }.hash;

    while x > h {
      p = unsafe { p.add(1) };
      x = unsafe { &*p }.hash;
    }

    if x != h { return None; }

    Some(unsafe { (&*p).value.assume_init_ref() })
  }

  #[inline]
  pub fn get_mut(&mut self, key: NonZeroU64) -> Option<&mut A> {
    let t = self.table as *mut Slot<A>;

    if t.is_null() { return None; }

    let m = self.mults;
    let s = self.shift;
    let h = hash(m, key);
    let i = spot(s, h);

    let mut p = unsafe { t.sub(i as usize) };
    let mut x = unsafe { &*p }.hash;

    while x > h {
      p = unsafe { p.add(1) };
      x = unsafe { &*p }.hash;
    }

    if x != h { return None; }

    Some(unsafe { (&mut *p).value.assume_init_mut() })
  }

  #[inline]
  pub fn insert(&mut self, key: NonZeroU64, value: A) -> Option<A> {
    let t = self.table as *mut Slot<A>;

    if t.is_null() { return self.insert_cold_null_table(key, value); }

    let m = self.mults;
    let s = self.shift;
    let h = hash(m, key);
    let i = spot(s, h);

    let mut p = unsafe { t.sub(i as usize) };
    let mut x = unsafe { &*p }.hash;

    while x > h {
      p = unsafe { p.add(1) };
      x = unsafe { &*p }.hash;
    }

    let v = mem::replace(&mut unsafe { &mut *p }.value, MaybeUninit::new(value));

    if x == h { return Some(unsafe { v.assume_init() }); }

    unsafe { &mut *p }.hash = h;

    let mut o = Slot { hash: x, value: v };

    while o.hash != 0 {
      p = unsafe { p.add(1) };
      o = unsafe { p.replace(o) };
    }

    let k = self.space - 1;
    self.space = k;

    let b = self.check;

    if k == 0 || ptr::eq(p, b) { return self.insert_cold_grow_table(); }

    None
  }

  #[inline(never)]
  #[cold]
  fn insert_cold_null_table(&mut self, key: NonZeroU64, value: A) -> Option<A> {
    // PRECONDITION:
    //
    // - The hashmap is unchanged since its creation by `new`.

    // The following asserts a constant expression.  Note that `size_of()`
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

    let a = unsafe { std::alloc::alloc_zeroed(layout) } as *mut Slot<A>;

    if a.is_null() { match std::alloc::handle_alloc_error(layout) {} }

    // Inserts into a fresh table. We know that this won't collide!

    let t = unsafe { a.add((1 << (64 - INITIAL_SHIFT)) - 1) };
    let b = unsafe { a.add(INITIAL_NUM_SLOTS - 1) };

    let m = self.mults;
    let h = hash(m, key);
    let i = spot(INITIAL_SHIFT, h);
    let p = unsafe { t.sub(i as usize) };

    unsafe { &mut *p }.hash = h;
    unsafe { &mut *p }.value = MaybeUninit::new(value);

    self.table = t;
    self.check = b;

    None
  }

  #[inline(never)]
  #[cold]
  fn insert_cold_grow_table(&mut self) -> Option<A> {
    let _ = self;
    /*
    let old_t = self.table;
    let old_s = self.shift;
    let old_k = self.space;
    let old_l = self.check;

    let new_s;
    let new_e;
    let new_k;

    if old_k == 0 {
      new_s = old_s - 1;
      new_k = 1 << (64 - old_s - 1);
    } else {
      new_s = old_s;
      new_k = old_k;
    }

    if unsafe { &*old_l }.hash != 0 {
      new_e = old_e + 1;
    } else {
      new_e = old_e;
    }

    let old_n = num_slots(old_s, old_e);
    let new_n = num_slots(new_s, new_e); // TODO: overflow?

    // TODO: better error?

    assert!(new_n <= isize::MAX as usize / mem::size_of::<Slot<A>>());

    let align = mem::align_of::<Slot<A>>();
    let old_size = old_n * mem::size_of::<Slot<A>>();
    let new_size = new_n * mem::size_of::<Slot<A>>();

    // SAFETY:
    //
    // - ???

    let old_layout = unsafe { Layout::from_size_align_unchecked(old_size, align) };
    let new_layout = unsafe { Layout::from_size_align_unchecked(new_size, align) };

    // SAFETY:
    //
    // - ???

    let new_t = unsafe { std::alloc::alloc_zeroed(new_layout) } as *mut Slot<A>;

    if new_t.is_null() { match std::alloc::handle_alloc_error(new_layout) {} }

    let new_l = unsafe { new_t.add(new_n - 1) };

    // TODO: initialize new_t

    self.table = new_t;
    self.shift = new_s;
    self.space = new_k;
    self.check = new_l;

    // SAFETY:
    //
    // - ???

    unsafe { std::alloc::dealloc(old_t as *mut u8, old_layout) };
    */

    None
  }

  #[inline]
  pub fn remove(&mut self, key: NonZeroU64) -> Option<A> {
    let t = self.table as *mut Slot<A>;

    if t.is_null() { return None; }

    let m = self.mults;
    let s = self.shift;
    let h = hash(m, key);
    let i = spot(s, h);

    let mut p = unsafe { t.sub(i as usize) };
    let mut x = unsafe { &*p }.hash;

    while x > h {
      p = unsafe { p.add(1) };
      x = unsafe { &*p }.hash;
    }

    if x != h { return None; }

    let v = unsafe { (&mut *p).value.assume_init_read() };

    let mut i: isize = i;

    loop {
      let o = unsafe { p.add(1).read() };
      let x = o.hash;

      if i > spot(s, x) || x == 0 {
        break; 
      }

      unsafe { p.write(o) };
      
      p = unsafe { p.add(1) };
      i = i - 1;
    }

    unsafe { &mut *p }.hash = 0;

    self.space = self.space + 1;

    Some(v)
  }

  pub fn clear(&mut self) {
    let t = self.table as *mut Slot<A>;

    if t.is_null() { return; }

    let s = self.shift;
    let b = self.check;
    let a = unsafe { t.sub((1 << (64 - s)) - 1) };
    let n = unsafe { b.offset_from(a) } as usize + 1;

    if mem::needs_drop::<A>() {
      for p in (0 .. n).map(|i| unsafe { a.add(i) }) {
        if unsafe { &mut *p }.hash != 0 {
          unsafe { &mut *p }.hash = 0;
          unsafe { (&mut *p).value.assume_init_drop() };
        }
      }
    } else {
      for p in (0 .. n).map(|i| unsafe { a.add(i) }) {
        unsafe { &mut *p }.hash = 0;
      }
    }
  }
}

impl<A> Drop for HashMapNZ64<A> {
  fn drop(&mut self) {
    let t = self.table as *mut Slot<A>;

    if t.is_null() { return; }

    let s = self.shift;
    let b = self.check;
    let a = unsafe { t.sub((1 << (64 - s)) - 1) };
    let n = unsafe { b.offset_from(a) } as usize + 1;

    if mem::needs_drop::<A>() {
      for p in (0 .. n).map(|i| unsafe { a.add(i) }) {
        if unsafe { &*p }.hash != 0 {
          unsafe { (&mut *p).value.assume_init_drop() };
        }
      }
    }

    let align = mem::align_of::<Slot<A>>();
    let size = n * mem::size_of::<Slot<A>>();
    let layout = unsafe { Layout::from_size_align_unchecked(size, align) };

    unsafe { std::alloc::dealloc(a as *mut u8, layout) };
  }
}
