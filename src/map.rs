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

const INITIAL_U: usize = 4;
const INITIAL_V: usize = 3;
const INITIAL_D: usize = 1 << INITIAL_U;
const INITIAL_E: usize = 1 << INITIAL_V;
const INITIAL_N: usize = INITIAL_D + INITIAL_E;
const INITIAL_S: usize = 64 - INITIAL_U;
const INITIAL_K: usize = INITIAL_D / 2;

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
const unsafe fn spot(shift: usize, h: u64) -> isize {
  if ! (shift <= 63) { unsafe { unreachable_unchecked() }; }
  (h >> shift) as isize 
}

impl<A> HashMapNZ64<A> {
  pub fn new() -> Self {
    Self {
      mults: Rng::with_thread_local(|g| [g.u64() | 1, g.u64() | 1]),
      table: ptr::null(),
      shift: INITIAL_S,
      space: INITIAL_K,
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

    let mut p = unsafe { t.offset(- spot(s, h)) };
    let mut x = unsafe { &*p }.hash;

    while ! (x <= h) {
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

    let mut p = unsafe { t.offset(- spot(s, h)) };
    let mut x = unsafe { &*p }.hash;

    while ! (x <= h) {
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

    let mut p = unsafe { t.offset(- spot(s, h)) };
    let mut x = unsafe { &*p }.hash;

    while ! (x <= h) {
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

    let mut p = unsafe { t.offset(- spot(s, h)) };
    let mut x = unsafe { &*p }.hash;

    while ! (x <= h) {
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
    assert!(INITIAL_N <= isize::MAX as usize / mem::size_of::<Slot<A>>());

    let align = mem::align_of::<Slot<A>>();
    let size = INITIAL_N * mem::size_of::<Slot<A>>();

    let layout = unsafe { Layout::from_size_align_unchecked(size, align) };

    let a = unsafe { std::alloc::alloc_zeroed(layout) } as *mut Slot<A>;

    if a.is_null() { match std::alloc::handle_alloc_error(layout) {} }

    let t = unsafe { a.add(INITIAL_D - 1) };
    let b = unsafe { a.add(INITIAL_N - 1) };

    let m = self.mults;
    let h = hash(m, key);
    let p = unsafe { t.offset(- spot(INITIAL_S, h)) };

    unsafe { &mut *p }.hash = h;
    unsafe { &mut *p }.value = MaybeUninit::new(value);

    self.table = t;
    self.space = INITIAL_K - 1;
    self.check = b;

    None
  }

  #[inline(never)]
  #[cold]
  fn insert_cold_grow_table(&mut self) -> Option<A> {
    let old_t = self.table;
    let old_s = self.shift;
    let old_k = self.space;
    let old_b = self.check;

    // d = 2 ** u
    // e = 2 ** v
    // n = d + e
    //
    // t = a + d - 1
    // b = a + n - 1

    let old_u = 64 - old_s;
    let old_d = 1 << old_u;
    let old_e = unsafe { old_b.offset_from(old_t) } as usize;
    let old_v = old_e.trailing_zeros() as usize;
    let old_n = old_d + old_e;
    let old_a = unsafe { old_t.sub(old_d - 1) };

    let new_u;
    let new_v;
    let new_k;

    if old_k == 0 {
      new_u = old_u + 1;
      new_k = old_d / 2;
    } else {
      new_u = old_u;
      new_k = old_k;
    }

    if unsafe { &*old_b }.hash != 0 {
      new_v = old_v + 1;
    } else {
      new_v = old_v;
    }

    assert!(1 <= new_u && new_u <= usize::BITS as usize - 1);
    assert!(1 <= new_v && new_v <= usize::BITS as usize - 2);

    let new_d = 1 << new_u;
    let new_e = 1 << new_v;
    let new_n = new_d + new_e;
    let new_s = 64 - new_u;

    assert!(new_n <= isize::MAX as usize / mem::size_of::<Slot<A>>());

    let align = mem::align_of::<Slot<A>>();

    let old_size = old_n * mem::size_of::<Slot<A>>();
    let new_size = new_n * mem::size_of::<Slot<A>>();

    let old_layout = unsafe { Layout::from_size_align_unchecked(old_size, align) };
    let new_layout = unsafe { Layout::from_size_align_unchecked(new_size, align) };

    let new_a = unsafe { std::alloc::alloc_zeroed(new_layout) } as *mut Slot<A>;

    if new_a.is_null() { match std::alloc::handle_alloc_error(new_layout) {} }

    let new_t = unsafe { new_a.add(new_d - 1) };
    let new_b = unsafe { new_a.add(new_n - 1) };

    let mut j = 0;

    for i in 0 .. old_n {
      let o = unsafe { old_a.add(i).read() };
      if o.hash == 0 { continue; }
      j = max(j, (! o.hash >> new_s) as usize);
      unsafe { new_a.add(j).write(o) };
      j = j + 1;
    }

    self.table = new_t;
    self.shift = new_s;
    self.space = new_k;
    self.check = new_b;

    unsafe { std::alloc::dealloc(old_a as *mut u8, old_layout) };

    None
  }

  #[inline]
  pub fn remove(&mut self, key: NonZeroU64) -> Option<A> {
    let t = self.table as *mut Slot<A>;

    if t.is_null() { return None; }

    let m = self.mults;
    let s = self.shift;
    let h = hash(m, key);

    let mut p = unsafe { t.offset(- spot(s, h)) };
    let mut x = unsafe { &*p }.hash;

    while ! (x <= h) {
      p = unsafe { p.add(1) };
      x = unsafe { &*p }.hash;
    }

    if x != h { return None; }

    let v = unsafe { (&mut *p).value.assume_init_read() };

    let mut i: isize = unsafe { spot(s, h) };

    loop {
      let o = unsafe { p.add(1).read() };
      let x = o.hash;

      if ! (i <= unsafe { spot(s, x) } && x != 0) { break; }

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
