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
const INITIAL_R: usize = INITIAL_D / 2;

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

const fn invert(x: u64) -> u64 {
  // https://arxiv.org/abs/2204.04342

  let a = x;
  let x = a.wrapping_mul(3) ^ 2;
  let y = 1u64.wrapping_sub(a.wrapping_mul(x));
  let x = x.wrapping_mul(y.wrapping_add(1));
  let y = y.wrapping_mul(y);
  let x = x.wrapping_mul(y.wrapping_add(1));
  let y = y.wrapping_mul(y);
  let x = x.wrapping_mul(y.wrapping_add(1));
  let y = y.wrapping_mul(y);
  let x = x.wrapping_mul(y.wrapping_add(1));
  x
}

const fn invert_hash_mults(x: [u64; 2]) -> [u64; 2] {
  let a = x[0];
  let b = x[1];
  let c = a.wrapping_mul(b);
  let c = invert(c);
  [ c.wrapping_mul(a), c.wrapping_mul(b) ]
}

#[inline(always)]
const unsafe fn spot(shift: usize, h: u64) -> isize {
  if ! (shift <= 63) { unsafe { unreachable_unchecked() }; }
  (h >> shift) as isize 
}

impl<A> HashMapNZ64<A> {
  pub fn new() -> Self {
    Self {
      mults: rng::u64x2().map(|m| (m | 1)),
      table: ptr::null(),
      shift: INITIAL_S,
      space: INITIAL_R,
      check: ptr::null(),
    }
  }

  pub fn with_random(rng: &mut Rng) -> Self {
    Self {
      mults: rng.u64x2().map(|m| (m | 1)),
      table: ptr::null(),
      shift: INITIAL_S,
      space: INITIAL_R,
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

    let mut p = unsafe { t.offset(- spot(s, h)) };
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

    let mut p = unsafe { t.offset(- spot(s, h)) };
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

    if t.is_null() { return self.insert_cold_init_table(key, value); }

    let m = self.mults;
    let s = self.shift;
    let h = hash(m, key);

    let mut p = unsafe { t.offset(- spot(s, h)) };
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

    let r = self.space - 1;
    self.space = r;

    let b = self.check;

    if r == 0 || ptr::eq(p, b) { return self.insert_cold_grow_table(); }

    None
  }

  #[inline(never)]
  #[cold]
  fn insert_cold_init_table(&mut self, key: NonZeroU64, value: A) -> Option<A> {
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
    self.space = INITIAL_R - 1;
    self.check = b;

    None
  }

  #[inline(never)]
  #[cold]
  fn insert_cold_grow_table(&mut self) -> Option<A> {
    let old_t = self.table as *mut Slot<A>;
    let old_s = self.shift;
    let old_r = self.space;
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
    let new_r;

    if old_r == 0 {
      new_u = old_u + 1;
      new_r = old_d / 2;
    } else {
      new_u = old_u;
      new_r = old_r;
    }

    if unsafe { &*old_b }.hash != 0 {
      new_v = old_v + 1;
    } else {
      new_v = old_v;
    }

    assert!(1 <= new_u && new_u <= usize::BITS as usize - 1 && new_u <= 64);
    assert!(1 <= new_v && new_v <= usize::BITS as usize - 2);

    let new_s = 64 - new_u;

    assert!(new_s <= 63);

    let new_d = 1 << new_u;
    let new_e = 1 << new_v;
    let new_n = new_d + new_e;

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

    each_mut(old_a, old_b, |p| {
      let x = unsafe { &*p }.hash;
      if x != 0 {
        j = max(j, (! x >> new_s) as usize);
        let q = unsafe { new_a.add(j) };
        unsafe { &mut *q }.hash = x;
        unsafe { &mut *q }.value = MaybeUninit::new(unsafe { (&*p).value.assume_init_read() });
        j = j + 1;
      }
    });

    self.table = new_t;
    self.shift = new_s;
    self.space = new_r;
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

    while x > h {
      p = unsafe { p.add(1) };
      x = unsafe { &*p }.hash;
    }

    if x != h { return None; }

    let v = unsafe { (&mut *p).value.assume_init_read() };

    loop {
      let q = unsafe { p.add(1) };
      let x = unsafe { &*q }.hash;

      if p < unsafe { t.offset(- spot(s, x)) } || x == 0 { break; }

      unsafe { &mut *p }.hash = x;
      unsafe { &mut *p }.value = MaybeUninit::new(unsafe { (&*q).value.assume_init_read() });

      p = q;
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
    let d = 1 << (64 - s);
    let a = unsafe { t.sub(d - 1) };

    if mem::needs_drop::<A>() {
      each_mut(a, b, |p| {
        if unsafe { &mut *p }.hash != 0 {
          unsafe { &mut *p }.hash = 0;
          unsafe { (&mut *p).value.assume_init_drop() };
        }
      })
    } else {
      each_mut(a, b, |p| { unsafe { &mut *p }.hash = 0; })
    }
  }

  pub fn sorted_keys(&self) -> Box<[NonZeroU64]> {
    let t = self.table;

    if t.is_null() { return Box::from([]); }

    let s = self.shift;
    let b = self.check;
    let d = 1 << (64 - s);
    let e = unsafe { b.offset_from(t) } as usize;
    let n = d + e;
    let a = unsafe { t.sub(d - 1) };
    let m = invert_hash_mults(self.mults);

    let mut r = Vec::with_capacity(n);

    each(a, b, |p| { 
      let x = unsafe { &*p }.hash;
      if x != 0 {
        let x = unsafe { NonZeroU64::new_unchecked(x) };
        let x = hash(m, x);
        let x = unsafe { NonZeroU64::new_unchecked(x) };
        r.push(x)
      }
    });

    let mut r = r.into_boxed_slice();
    r.sort();
    r
  }

  pub fn items_sorted_by_key(&self) -> Box<[(NonZeroU64, &A)]> {
    let t = self.table;

    if t.is_null() { return Box::from([]); }

    let s = self.shift;
    let b = self.check;
    let d = 1 << (64 - s);
    let e = unsafe { b.offset_from(t) } as usize;
    let n = d + e;
    let a = unsafe { t.sub(d - 1) };
    let m = invert_hash_mults(self.mults);

    let mut r = Vec::with_capacity(n);

    each(a, b, |p| { 
      let x = unsafe { &*p }.hash;
      if x != 0 {
        let x = unsafe { NonZeroU64::new_unchecked(x) };
        let x = hash(m, x);
        let x = unsafe { NonZeroU64::new_unchecked(x) };
        let v = unsafe { (&*p).value.assume_init_ref() };
        r.push((x, v))
      }
    });

    let mut r = r.into_boxed_slice();
    r.sort_by_key(|a| a.0);
    r
  }

  pub fn items_sorted_by_key_mut(&mut self) -> Box<[(NonZeroU64, &mut A)]> {
    let t = self.table as *mut Slot<A>;

    if t.is_null() { return Box::from([]); }

    let s = self.shift;
    let b = self.check;
    let d = 1 << (64 - s);
    let e = unsafe { b.offset_from(t) } as usize;
    let n = d + e;
    let a = unsafe { t.sub(d - 1) };
    let m = invert_hash_mults(self.mults);

    let mut r = Vec::with_capacity(n);

    each_mut(a, b, |p| { 
      let x = unsafe { &*p }.hash;
      if x != 0 {
        let x = unsafe { NonZeroU64::new_unchecked(x) };
        let x = hash(m, x);
        let x = unsafe { NonZeroU64::new_unchecked(x) };
        let v = unsafe { (&mut *p).value.assume_init_mut() };
        r.push((x, v))
      }
    });

    let mut r = r.into_boxed_slice();
    r.sort_by_key(|a| a.0);
    r
  }
}

impl<A> Drop for HashMapNZ64<A> {
  fn drop(&mut self) {
    let t = self.table as *mut Slot<A>;

    if t.is_null() { return; }

    let s = self.shift;
    let b = self.check;
    let d = 1 << (64 - s);
    let e = unsafe { b.offset_from(t) } as usize;
    let n = d + e;
    let a = unsafe { t.sub(d - 1) };

    if mem::needs_drop::<A>() {
      each_mut(a, b, |p| {
        if unsafe { &*p }.hash != 0 {
          unsafe { (&mut *p).value.assume_init_drop() };
        }
      })
    }

    let align = mem::align_of::<Slot<A>>();
    let size = n * mem::size_of::<Slot<A>>();
    let layout = unsafe { Layout::from_size_align_unchecked(size, align) };

    unsafe { std::alloc::dealloc(a as *mut u8, layout) };
  }
}

impl<A: fmt::Debug> fmt::Debug for HashMapNZ64<A> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
    let mut f = f.debug_map();

    for (key, value) in self.items_sorted_by_key().iter() {
      f.entry(key, value);
    }

    f.finish()
  }
}
