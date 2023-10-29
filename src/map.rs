//! This module implements a fast hash map keyed by `NonZeroU64`s.

use crate::prelude::*;

/// A fast hash map keyed by `NonZeroU64`s.

pub struct HashMapNZ64<T> {
  mixer: Mixer,
  table: *const Slot<T>, // covariant in `T`
  shift: usize,
  space: isize,
  check: *const Slot<T>,
}

unsafe impl<T: Send> Send for HashMapNZ64<T> {}

unsafe impl<T: Sync> Sync for HashMapNZ64<T> {}

#[derive(Clone, Copy)]
struct Mixer(u64, u64);

struct Slot<T> {
  hash: u64,
  value: MaybeUninit<T>,
}

const INITIAL_S: usize = 60;                        // shift
const INITIAL_C: isize = 1 << (64 - INITIAL_S - 1); // capacity
const INITIAL_D: usize = 1 << (64 - INITIAL_S);     // table length, primary
const INITIAL_E: usize = 8;                         // extra slots
const INITIAL_N: usize = INITIAL_D + INITIAL_E;     // table length, total
const INITIAL_R: isize = INITIAL_C;                 // remaining capacity

#[inline(always)]
unsafe fn spot(shift: usize, h: u64) -> isize {
  unsafe { assume(shift <= 63) };
  (h >> shift) as isize
}

#[inline(always)]
const fn invert(a: u64) -> u64 {
  // https://arxiv.org/abs/2204.04342

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

impl Mixer {
  #[inline(always)]
  fn new(m: u64) -> Self {
    let a = m | 1;
    let b = invert(a);
    Self(a, b)
  }

  #[inline(always)]
  const fn hash(self, x: NonZeroU64) -> NonZeroU64 {
    let a = self.0;
    let b = self.1;
    let x = x.get();
    let x = x.wrapping_mul(a);
    let x = x.swap_bytes();
    let x = x.wrapping_mul(b);
    unsafe { NonZeroU64::new_unchecked(x) }
  }
}

impl<T> HashMapNZ64<T> {
  const EMPTY: [Slot<T>; 10] = [
    Slot { hash: 0, value: MaybeUninit::uninit() },
    Slot { hash: 0, value: MaybeUninit::uninit() },
    Slot { hash: 0, value: MaybeUninit::uninit() },
    Slot { hash: 0, value: MaybeUninit::uninit() },
    Slot { hash: 0, value: MaybeUninit::uninit() },
    Slot { hash: 0, value: MaybeUninit::uninit() },
    Slot { hash: 0, value: MaybeUninit::uninit() },
    Slot { hash: 0, value: MaybeUninit::uninit() },
    Slot { hash: 0, value: MaybeUninit::uninit() },
    Slot { hash: 0, value: MaybeUninit::uninit() },
  ];

  /// Creates an empty map, seeding the hash mixer from a thread-local random
  /// number generator.

  #[inline(always)]
  pub fn new() -> Self {
    rng::thread_local::with(|rng| Self::new_seeded(rng))
  }

  /// Creates an empty map, seeding the hash mixer from the given random number
  /// generator.

  #[inline(always)]
  pub fn new_seeded(rng: &mut Rng) -> Self {
    let t = &Self::EMPTY as *const Slot<T>;

    Self {
      mixer: Mixer::new(rng.u64()),
      table: t.wrapping_add(1),
      shift: 63,
      space: 1,
      check: t.wrapping_add(9),
    }
  }

  /// Returns the number of items.

  #[inline(always)]
  pub fn len(&self) -> usize {
    let s = self.shift;
    let r = self.space;
    let c = 1 << (64 - s - 1);
    let k = (c - r) as usize;
    k
  }

  /// Returns whether the map contains zero items.

  #[inline(always)]
  pub fn is_empty(&self) -> bool {
    self.len() == 0
  }

  /// Returns whether the map contains the given key.

  #[inline(always)]
  pub fn contains_key(&self, key: NonZeroU64) -> bool {
    let t = self.table;
    let m = self.mixer;
    let s = self.shift;
    let h = u64::from(m.hash(key));

    let mut p = unsafe { t.offset(- spot(s, h)) };
    let mut x = unsafe { &*p }.hash;

    while x > h {
      p = unsafe { p.add(1) };
      x = unsafe { &*p }.hash;
    }

    x == h
  }

  /// Returns a reference to the value associated with the given key, if
  /// present.

  #[inline(always)]
  pub fn get(&self, key: NonZeroU64) -> Option<&T> {
    let t = self.table;
    let m = self.mixer;
    let s = self.shift;
    let h = u64::from(m.hash(key));

    let mut p = unsafe { t.offset(- spot(s, h)) };
    let mut x = unsafe { &*p }.hash;

    while x > h {
      p = unsafe { p.add(1) };
      x = unsafe { &*p }.hash;
    }

    if x != h { return None; }

    Some(unsafe { (&*p).value.assume_init_ref() })
  }

  /// Returns a mutable reference to the value associated with the given key,
  /// if present.

  #[inline(always)]
  pub fn get_mut(&mut self, key: NonZeroU64) -> Option<&mut T> {
    let t = self.table as *mut Slot<T>;
    let m = self.mixer;
    let s = self.shift;
    let h = u64::from(m.hash(key));

    let mut p = unsafe { t.offset(- spot(s, h)) };
    let mut x = unsafe { &*p }.hash;

    while x > h {
      p = unsafe { p.add(1) };
      x = unsafe { &*p }.hash;
    }

    if x != h { return None; }

    Some(unsafe { (&mut *p).value.assume_init_mut() })
  }

  #[inline(never)]
  #[cold]
  unsafe fn internal_init_table_and_insert(&mut self, key: NonZeroU64, value: T) {
    assert!(INITIAL_N <= isize::MAX as usize / mem::size_of::<Slot<T>>());

    let align = mem::align_of::<Slot<T>>();
    let size = INITIAL_N * mem::size_of::<Slot<T>>();
    let layout = unsafe { Layout::from_size_align_unchecked(size, align) };

    let a = unsafe { alloc::alloc::alloc_zeroed(layout) } as *mut Slot<T>;
    if a.is_null() { match alloc::alloc::handle_alloc_error(layout) {} }

    let t = unsafe { a.add(INITIAL_D - 1) };
    let z = unsafe { a.add(INITIAL_N - 1) };

    let m = self.mixer;
    let h = u64::from(m.hash(key));
    let p = unsafe { t.offset(- spot(INITIAL_S, h)) };

    unsafe { &mut *p }.hash = h;
    unsafe { &mut *p }.value = MaybeUninit::new(value);

    // We only modify `self` after we know that allocation has succeeded.

    self.table = t;
    self.shift = INITIAL_S;
    self.space = INITIAL_R - 1;
    self.check = z;
  }

  #[inline(never)]
  #[cold]
  unsafe fn internal_grow_table(&mut self) {
    let old_t = self.table as *mut Slot<T>;
    let old_s = self.shift;
    let old_r = self.space;
    let old_z = self.check as *mut Slot<T>;

    let old_z_hash = unsafe { &*old_z }.hash;
    let is_overfull = old_r < 0;
    let is_overflow = old_z_hash != 0;

    // WARNING!
    //
    // We must be careful to leave the map in a valid state even if attempting
    // to allocate a new table results in a panic.
    //
    // It turns out that the `is_overfull` state with negative space actually
    // *is* valid, but the `is_overflow` state *is not* valid.
    //
    // In the latter case, we temporarily remove the item in the final slot and
    // restore it after we have succeeded at everything that might panic.
    //
    // This is an instance of the infamous PPYP design pattern.

    if is_overflow {
      unsafe { &mut *old_z }.hash = 0;
      self.space = old_r + 1;
    }

    let old_c = 1 << (64 - old_s - 1);
    let old_d = 1 << (64 - old_s);
    let old_e = unsafe { old_z.offset_from(old_t) } as usize;
    let old_n = old_d + old_e;
    let old_a = unsafe { old_t.sub(old_d - 1) };
    let old_u = 64 - old_s;
    let old_v = old_e.trailing_zeros() as usize;

    let new_u = old_u + is_overfull as usize;
    let new_v = old_v + is_overflow as usize;

    assert!(new_u <= 64);
    assert!(new_u <= usize::BITS as usize - 1);
    assert!(new_v <= usize::BITS as usize - 2);

    let new_s = 64 - new_u;
    let new_c = 1 << (64 - new_s - 1);
    let new_d = 1 << (64 - new_s);
    let new_e = 1 << new_v;
    let new_n = new_d + new_e;
    let new_r = old_r + (new_c - old_c);

    assert!(new_n <= isize::MAX as usize / mem::size_of::<Slot<T>>());

    let align = mem::align_of::<Slot<T>>();
    let old_size = old_n * mem::size_of::<Slot<T>>();
    let new_size = new_n * mem::size_of::<Slot<T>>();
    let old_layout = unsafe { Layout::from_size_align_unchecked(old_size, align) };
    let new_layout = unsafe { Layout::from_size_align_unchecked(new_size, align) };

    let new_a = unsafe { alloc::alloc::alloc_zeroed(new_layout) } as *mut Slot<T>;
    if new_a.is_null() { match alloc::alloc::handle_alloc_error(new_layout) {} }

    // At this point, we know that allocating a new table has succeeded, so we
    // undo our earlier `if is_overflow { ... }` block.

    if is_overflow {
      unsafe { &mut *old_z }.hash = old_z_hash;
      self.space = old_r;
    }

    let new_t = unsafe { new_a.add(new_d - 1) };
    let new_z = unsafe { new_a.add(new_n - 1) };

    let mut p = old_a;
    let mut q = new_a;

    while p <= old_z {
      let x = unsafe { &*p }.hash;

      if x != 0 {
        q = max(q, unsafe { new_t.offset(- spot(new_s, x)) });
        unsafe { &mut *q }.hash = x;
        unsafe { &mut *q }.value = MaybeUninit::new(unsafe { (&*p).value.assume_init_read() });
        q = unsafe { q.add(1) };
      }

      p = unsafe { p.add(1) };
    }

    self.table = new_t;
    self.shift = new_s;
    self.space = new_r;
    self.check = new_z;

    // The map is now in a valid state, even if `dealloc` panics.

    unsafe { alloc::alloc::dealloc(old_a as *mut u8, old_layout) };
  }

  /// Inserts the given key and value into the map. Returns the previous value
  /// associated with given key, if one was present.
  ///
  /// # Panics
  ///
  /// Panics when allocation fails. If that happens, it is possible for the map
  /// to leak an arbitrary set of items, but the map will remain in a valid
  /// state.

  #[inline(always)]
  pub fn insert(&mut self, key: NonZeroU64, value: T) -> Option<T> {
    let s = self.shift;

    if s == 63 {
      unsafe { self.internal_init_table_and_insert(key, value) };
      return None;
    }

    let t = self.table as *mut Slot<T>;
    let z = self.check as *mut Slot<T>;
    let m = self.mixer;

    let h = u64::from(m.hash(key));

    let mut p = unsafe { t.offset(- spot(s, h)) };
    let mut x = unsafe { &*p }.hash;

    while x > h {
      p = unsafe { p.add(1) };
      x = unsafe { &*p }.hash;
    }

    if x == h {
      let v = mem::replace(unsafe { (&mut *p).value.assume_init_mut() }, value);
      return Some(v);
    }

    let mut v = value;

    unsafe { &mut *p }.hash = h;

    while x != 0 {
      v = mem::replace(unsafe { (&mut *p).value.assume_init_mut() }, v);
      p = unsafe { p.add(1) };
      x = mem::replace(&mut unsafe { &mut *p }.hash, x);
    }

    unsafe { &mut *p }.value = MaybeUninit::new(v);

    let r = self.space - 1;
    self.space = r;

    if r < 0 || p == z { unsafe { self.internal_grow_table() }; }

    None
  }

  /// Removes the given key from the map. Returns the previous value associated
  /// with the given key, if one was present.

  #[inline(always)]
  pub fn remove(&mut self, key: NonZeroU64) -> Option<T> {
    let t = self.table as *mut Slot<T>;
    let m = self.mixer;
    let s = self.shift;
    let h = u64::from(m.hash(key));

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

      if p < unsafe { t.offset(- spot(s, x)) } || expect(x == 0, false) { break; }

      unsafe { &mut *p }.hash = x;
      unsafe { &mut *p }.value = MaybeUninit::new(unsafe { (&*q).value.assume_init_read() });

      p = q;
    }

    unsafe { &mut *p }.hash = 0;
    self.space += 1;

    Some(v)
  }

  #[inline(always)]
  pub fn entry(&mut self, key: NonZeroU64) -> Entry<'_, T> {
    let t = self.table as *mut Slot<T>;
    let m = self.mixer;
    let s = self.shift;
    let h = u64::from(m.hash(key));

    let mut p = unsafe { t.offset(- spot(s, h)) };
    let mut x = unsafe { &*p }.hash;

    while x > h {
      p = unsafe { p.add(1) };
      x = unsafe { &*p }.hash;
    }

    if x == h {
      Entry::Occupied(OccupiedEntry { map: self, ptr: p, })
    } else {
      Entry::Vacant(VacantEntry { map: self, key })
    }
  }

  /// Removes every item from the map. Retains heap-allocated memory.

  pub fn clear(&mut self) {
    let s = self.shift;

    if s == 63 { return; }

    let t = self.table as *mut Slot<T>;
    let z = self.check as *mut Slot<T>;
    let r = self.space;
    let c = 1 << (64 - s - 1);
    let d = 1 << (64 - s);
    let a = unsafe { t.sub(d - 1) };
    let k = (c - r) as usize;

    if k == 0 { return; }

    if mem::needs_drop::<T>() {
      // WARNING!
      //
      // We must be careful to leave the map in a valid state even if a call to
      // `drop` panics.
      //
      // Here, we traverse the table in reverse order to ensure that we don't
      // remove an item that is currently displacing another item.
      //
      // Also, we update `self.space` as we go instead of once at the end.

      let mut p = z;
      let mut k = k;
      let mut r = r;

      loop {
        p = unsafe { p.sub(1) };

        if unsafe { &mut *p }.hash != 0 {
          unsafe { &mut *p }.hash = 0;
          k -= 1;
          r += 1;
          self.space = r;
          unsafe { (&mut *p).value.assume_init_drop() };
          if k == 0 { break; }
        }
      }
    } else {
      let mut p = a;

      while p <= z {
        unsafe { &mut *p }.hash = 0;
        p = unsafe { p.add(1) };
      }

      self.space = c;
    }
  }

  /// Removes every item from the map. Releases heap-allocated memory.

  pub fn reset(&mut self) {
    let s = self.shift;

    if s == 63 { return; }

    let t = self.table as *mut Slot<T>;
    let z = self.check as *mut Slot<T>;
    let d = 1 << (64 - s);
    let e = unsafe { z.offset_from(t) } as usize;
    let n = d + e;
    let a = unsafe { t.sub(d - 1) };

    self.table = ptr::null();
    self.shift = INITIAL_S;
    self.space = INITIAL_R;
    self.check = ptr::null();

    if mem::needs_drop::<T>() {
      // WARNING!
      //
      // We must be careful to leave the map in a valid state even if a call to
      // `drop` panics.
      //
      // Here, we have already put `self` into the valid initial state, so if a
      // call to `drop` panics then we can just safely leak the table.

      let mut p = a;

      while p <= z {
        if unsafe { &mut *p }.hash != 0 {
          unsafe { (&mut *p).value.assume_init_drop() };
        }
        p = unsafe { p.add(1) };
      }
    }

    let align = mem::align_of::<Slot<T>>();
    let size = n * mem::size_of::<Slot<T>>();
    let layout = unsafe { Layout::from_size_align_unchecked(size, align) };

    unsafe { alloc::alloc::dealloc(a as *mut u8, layout) };
  }

  /// Returns an iterator yielding each key and a reference to its associated
  /// value. The iterator item type is `(NonZeroU64, &'_ T)`.

  pub fn iter(&self) -> Iter<'_, T> {
    let m = self.mixer;
    let s = self.shift;
    let r = self.space;
    let z = self.check;
    let c = 1 << (64 - s - 1);
    let k = (c - r) as usize;

    Iter { len: k, ptr: z, rev: m, var: PhantomData }
  }

  /// Returns an iterator yielding each key and a mutable reference to its
  /// associated value. The iterator item type is `(NonZeroU64, &'_ mut T)`.

  pub fn iter_mut(&mut self) -> IterMut<'_, T> {
    let m = self.mixer;
    let s = self.shift;
    let r = self.space;
    let z = self.check as *mut Slot<T>;
    let c = 1 << (64 - s - 1);
    let k = (c - r) as usize;

    IterMut { len: k, ptr: z, rev: m, var: PhantomData }
  }

  /// Returns an iterator yielding each key. The iterator item type is
  /// `NonZeroU64`.

  pub fn keys(&self) -> Keys<'_, T> {
    let m = self.mixer;
    let s = self.shift;
    let r = self.space;
    let z = self.check;
    let c = 1 << (64 - s - 1);
    let k = (c - r) as usize;

    Keys { len: k, ptr: z, rev: m, var: PhantomData }
  }

  /// Returns an iterator yielding a reference to each value. The iterator item
  /// type is `&'_ T`.

  pub fn values(&self) -> Values<'_, T> {
    let s = self.shift;
    let r = self.space;
    let z = self.check;
    let c = 1 << (64 - s - 1);
    let k = (c - r) as usize;

    Values { len: k, ptr: z, var: PhantomData }
  }

  /// Returns an iterator yielding a mutable reference to each value. The
  /// iterator item type is `&'_ mut T`.

  pub fn values_mut(&mut self) -> ValuesMut<'_, T> {
    let s = self.shift;
    let r = self.space;
    let z = self.check as *mut Slot<T>;
    let c = 1 << (64 - s - 1);
    let k = (c - r) as usize;

    ValuesMut { len: k, ptr: z, var: PhantomData }
  }

  /// Returns an iterator yielding each value and consuming the map. The
  /// iterator item type is `T`.

  pub fn into_values(self) -> IntoValues<T> {
    let o = ManuallyDrop::new(self);
    let s = o.shift;

    if s == 63 { return IntoValues { len: 0, ptr: ptr::null(), mem: (ptr::null_mut(), 0) }; }

    let t = o.table;
    let z = o.check;
    let r = o.space;
    let c = 1 << (64 - s - 1);
    let d = 1 << (64 - s);
    let e = unsafe { z.offset_from(t) } as usize;
    let n = d + e;
    let k = (c - r) as usize;
    let a = unsafe { t.sub(d - 1) } as *mut u8;

    IntoValues { len: k, ptr: z, mem: (a, n * mem::size_of::<Slot<T>>()) }
  }

  fn internal_num_slots(&self) -> usize {
    let s = self.shift;

    if s == 63 { return 0; }

    let t = self.table;
    let z = self.check;
    let z = self.check;
    let d = 1 << (64 - s);
    let e = unsafe { z.offset_from(t) } as usize;
    let n = d + e;
    n
  }

  fn internal_num_bytes(&self) -> usize {
    self.internal_num_slots() * mem::size_of::<Slot<T>>()
  }

  fn internal_load(&self) -> f64 {
    let k = self.len();
    let n = self.internal_num_slots();

    if n == 0 { return 0.; }

    (k as f64) / (n as f64)
  }

  fn internal_allocation_info(&self) -> Option<(NonNull<u8>, Layout)> {
    let s = self.shift;

    if s == 63 { return None; }

    let t = self.table;
    let z = self.check;
    let d = 1 << (64 - s);
    let e = unsafe { z.offset_from(t) } as usize;
    let n = d + e;
    let a = unsafe { t.sub(d - 1) };

    let align = mem::align_of::<Slot<T>>();
    let size = n * mem::size_of::<Slot<T>>();
    let layout = unsafe { Layout::from_size_align_unchecked(size, align) };

    Some((unsafe { NonNull::new_unchecked(a as *mut u8) }, layout))
  }
}

impl<T> Drop for HashMapNZ64<T> {
  fn drop(&mut self) {
    let _ = self;
    // self.reset()
  }
}

impl<T> Index<NonZeroU64> for HashMapNZ64<T> {
  type Output = T;

  #[inline(always)]
  fn index(&self, key: NonZeroU64) -> &T {
    self.get(key).unwrap()
  }
}

impl<T> IndexMut<NonZeroU64> for HashMapNZ64<T> {
  #[inline(always)]
  fn index_mut(&mut self, key: NonZeroU64) -> &mut T {
    self.get_mut(key).unwrap()
  }
}

pub struct OccupiedEntry<'a, T: 'a> {
  map: &'a mut HashMapNZ64<T>,
  ptr: *mut Slot<T>,
}

pub struct VacantEntry<'a, T: 'a> {
  map: &'a mut HashMapNZ64<T>,
  key: NonZeroU64,
}

pub enum Entry<'a, T: 'a> {
  Occupied(OccupiedEntry<'a, T>),
  Vacant(VacantEntry<'a, T>),
}

/// Iterator returned by [`HashMapNZ64::iter`].

#[derive(Clone)]
pub struct Iter<'a, T: 'a> {
  len: usize,
  ptr: *const Slot<T>,
  rev: Mixer,
  var: PhantomData<&'a T>,
}

/// Iterator returned by [`HashMapNZ64::iter_mut`].

pub struct IterMut<'a, T: 'a> {
  len: usize,
  ptr: *mut Slot<T>,
  rev: Mixer,
  var: PhantomData<&'a mut T>,
}

/// Iterator returned by [`HashMapNZ64::keys`].

#[derive(Clone)]
pub struct Keys<'a, T: 'a> {
  len: usize,
  ptr: *const Slot<T>,
  rev: Mixer,
  var: PhantomData<&'a T>,
}

/// Iterator returned by [`HashMapNZ64::values`].

#[derive(Clone)]
pub struct Values<'a, T: 'a> {
  len: usize,
  ptr: *const Slot<T>,
  var: PhantomData<&'a T>,
}

/// Iterator returned by [`HashMapNZ64::values_mut`].

pub struct ValuesMut<'a, T: 'a> {
  len: usize,
  ptr: *mut Slot<T>,
  var: PhantomData<&'a mut T>,
}

/// Iterator returned by [`HashMapNZ64::into_iter`].

pub struct IntoIter<T> {
  rev: Mixer,
  len: usize,
  ptr: *const Slot<T>, // covariant in `T`
  mem: (*mut u8, usize),
}

/// Iterator returned by [`HashMapNZ64::into_values`].

pub struct IntoValues<T> {
  len: usize,
  ptr: *const Slot<T>, // covariant in `T`
  mem: (*mut u8, usize),
}

impl<'a, T> FusedIterator for Iter<'a, T> {}

impl<'a, T> FusedIterator for IterMut<'a, T> {}

impl<'a, T> FusedIterator for Keys<'a, T> {}

impl<'a, T> FusedIterator for Values<'a, T> {}

impl<'a, T> FusedIterator for ValuesMut<'a, T> {}

impl<'a, T> ExactSizeIterator for Iter<'a, T> {}

impl<'a, T> ExactSizeIterator for IterMut<'a, T> {}

impl<'a, T> ExactSizeIterator for Keys<'a, T> {}

impl<'a, T> ExactSizeIterator for Values<'a, T> {}

impl<'a, T> ExactSizeIterator for ValuesMut<'a, T> {}

impl<T> IntoIterator for HashMapNZ64<T> {
  type Item = (NonZeroU64, T);

  type IntoIter = IntoIter<T>;

  fn into_iter(self) -> IntoIter<T> {
    let o = ManuallyDrop::new(self);
    let s = o.shift;
    let m = o.mixer;

    if s == 63 { return IntoIter { rev: m, len: 0, ptr: ptr::null(), mem: (ptr::null_mut(), 0) }; }

    let t = o.table;
    let z = o.check;
    let r = o.space;
    let c = 1 << (64 - s - 1);
    let d = 1 << (64 - s);
    let e = unsafe { z.offset_from(t) } as usize;
    let n = d + e;
    let k = (c - r) as usize;
    let a = unsafe { t.sub(d - 1) } as *mut u8;

    IntoIter { rev: m, len: k, ptr: z, mem: (a, n * mem::size_of::<Slot<T>>()) }
  }
}

impl<T: fmt::Debug> fmt::Debug for HashMapNZ64<T> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
    let mut items = self.iter().collect::<Vec<(NonZeroU64, &T)>>();

    items.sort_by_key(|x| x.0);

    let mut f = f.debug_map();

    for (key, value) in items.iter() {
      let _: _ = f.entry(key, value);
    }

    f.finish()
  }
}

impl<'a, T> OccupiedEntry<'a, T> {
  #[inline(always)]
  pub fn get(&self) -> &T {
    unsafe { (&*self.ptr).value.assume_init_ref() }
  }

  #[inline(always)]
  pub fn get_mut(&mut self) -> &mut T {
    unsafe { (&mut *self.ptr).value.assume_init_mut() }
  }

  #[inline(always)]
  pub fn into_mut(self) -> &'a mut T {
    unsafe { (&mut *self.ptr).value.assume_init_mut() }
  }

  #[inline(always)]
  pub fn insert(&mut self, value: T) -> T {
    mem::replace(self.get_mut(), value)
  }

  #[inline(always)]
  pub fn remove(self) -> T {
    let mut p = self.ptr;
    let o = self.map;
    let t = o.table as *mut Slot<T>;
    let s = o.shift;

    let v = unsafe { (&mut *p).value.assume_init_read() };

    loop {
      let q = unsafe { p.add(1) };
      let x = unsafe { &*q }.hash;

      if p < unsafe { t.offset(- spot(s, x)) } || expect(x == 0, false) { break; }

      unsafe { &mut *p }.hash = x;
      unsafe { &mut *p }.value = MaybeUninit::new(unsafe { (&*q).value.assume_init_read() });

      p = q;
    }

    unsafe { &mut *p }.hash = 0;
    o.space += 1;

    v
  }
}


impl<'a, T> VacantEntry<'a, T> {
  pub fn insert(self, value: T) -> &'a mut T {
    // TODO: make this efficient

    let _: _ = self.map.insert(self.key, value);
    self.map.get_mut(self.key).unwrap()
  }
}

impl<'a, T> Iterator for Iter<'a, T> {
  type Item = (NonZeroU64, &'a T);

  #[inline(always)]
  fn next(&mut self) -> Option<Self::Item> {
    let k = self.len;

    if k == 0 { return None; }

    let mut p = unsafe { self.ptr.sub(1) };
    let mut x = unsafe { &*p }.hash;

    while x == 0 {
      p = unsafe { p.sub(1) };
      x = unsafe { &*p }.hash;
    }

    let x = self.rev.hash(unsafe { NonZeroU64::new_unchecked(x) });
    let v = unsafe { (&*p).value.assume_init_ref() };

    self.len = k - 1;
    self.ptr = p;

    Some((x, v))
  }

  #[inline(always)]
  fn size_hint(&self) -> (usize, Option<usize>) {
    (self.len, Some(self.len))
  }
}

impl<'a, T> Iterator for IterMut<'a, T> {
  type Item = (NonZeroU64, &'a mut T);

  #[inline(always)]
  fn next(&mut self) -> Option<Self::Item> {
    let k = self.len;

    if k == 0 { return None; }

    let mut p = unsafe { self.ptr.sub(1) };
    let mut x = unsafe { &*p }.hash;

    while x == 0 {
      p = unsafe { p.sub(1) };
      x = unsafe { &*p }.hash;
    }

    let x = self.rev.hash(unsafe { NonZeroU64::new_unchecked(x) });
    let v = unsafe { (&mut *p).value.assume_init_mut() };

    self.len = k - 1;
    self.ptr = p;

    Some((x, v))
  }

  #[inline(always)]
  fn size_hint(&self) -> (usize, Option<usize>) {
    (self.len, Some(self.len))
  }
}

impl<'a, T> Iterator for Keys<'a, T> {
  type Item = NonZeroU64;

  #[inline(always)]
  fn next(&mut self) -> Option<Self::Item> {
    let k = self.len;

    if k == 0 { return None; }

    let mut p = unsafe { self.ptr.sub(1) };
    let mut x = unsafe { &*p }.hash;

    while x == 0 {
      p = unsafe { p.sub(1) };
      x = unsafe { &*p }.hash;
    }

    let x = self.rev.hash(unsafe { NonZeroU64::new_unchecked(x) });

    self.len = k - 1;
    self.ptr = p;

    Some(x)
  }

  #[inline(always)]
  fn size_hint(&self) -> (usize, Option<usize>) {
    (self.len, Some(self.len))
  }
}

impl<'a, T> Iterator for Values<'a, T> {
  type Item = &'a T;

  #[inline(always)]
  fn next(&mut self) -> Option<Self::Item> {
    let k = self.len;

    if k == 0 { return None; }

    let mut p = unsafe { self.ptr.sub(1) };
    let mut x = unsafe { &*p }.hash;

    while x == 0 {
      p = unsafe { p.sub(1) };
      x = unsafe { &*p }.hash;
    }

    let v = unsafe { (&*p).value.assume_init_ref() };

    self.len = k - 1;
    self.ptr = p;

    Some(v)
  }

  #[inline(always)]
  fn size_hint(&self) -> (usize, Option<usize>) {
    (self.len, Some(self.len))
  }
}

impl<'a, T> Iterator for ValuesMut<'a, T> {
  type Item = &'a mut T;

  #[inline(always)]
  fn next(&mut self) -> Option<Self::Item> {
    let k = self.len;

    if k == 0 { return None; }

    let mut p = unsafe { self.ptr.sub(1) };
    let mut x = unsafe { &*p }.hash;

    while x == 0 {
      p = unsafe { p.sub(1) };
      x = unsafe { &*p }.hash;
    }

    let v = unsafe { (&mut *p).value.assume_init_mut() };

    self.len = k - 1;
    self.ptr = p;

    Some(v)
  }

  #[inline(always)]
  fn size_hint(&self) -> (usize, Option<usize>) {
    (self.len, Some(self.len))
  }
}

impl<T> Iterator for IntoIter<T> {
  type Item = (NonZeroU64, T);

  #[inline(always)]
  fn next(&mut self) -> Option<Self::Item> {
    let k = self.len;

    if k == 0 { return None; }

    let mut p = unsafe { self.ptr.sub(1) };
    let mut x = unsafe { &*p }.hash;

    while x == 0 {
      p = unsafe { p.sub(1) };
      x = unsafe { &*p }.hash;
    }

    let x = self.rev.hash(unsafe { NonZeroU64::new_unchecked(x) });
    let v = unsafe { (&*p).value.assume_init_read() };

    self.len = k - 1;
    self.ptr = p;

    Some((x, v))
  }

  #[inline(always)]
  fn size_hint(&self) -> (usize, Option<usize>) {
    (self.len, Some(self.len))
  }
}

impl<T> Drop for IntoIter<T> {
  fn drop(&mut self) {
    for (_, v) in &mut *self { drop::<T>(v) }

    if ! self.mem.0.is_null() {
      let size = self.mem.1;
      let align = mem::align_of::<Slot<T>>();
      let layout = unsafe { Layout::from_size_align_unchecked(size, align) };

      unsafe { alloc::alloc::dealloc(self.mem.0, layout) };
    }
  }
}

impl<T> Iterator for IntoValues<T> {
  type Item = T;

  #[inline(always)]
  fn next(&mut self) -> Option<Self::Item> {
    let k = self.len;

    if k == 0 { return None; }

    let mut p = unsafe { self.ptr.sub(1) };
    let mut x = unsafe { &*p }.hash;

    while x == 0 {
      p = unsafe { p.sub(1) };
      x = unsafe { &*p }.hash;
    }

    let v = unsafe { (&*p).value.assume_init_read() };

    self.ptr = p;
    self.len = k - 1;

    Some(v)
  }

  #[inline(always)]
  fn size_hint(&self) -> (usize, Option<usize>) {
    (self.len, Some(self.len))
  }
}

impl<T> Drop for IntoValues<T> {
  fn drop(&mut self) {
    for v in &mut *self { drop::<T>(v) }

    if ! self.mem.0.is_null() {
      let size = self.mem.1;
      let align = mem::align_of::<Slot<T>>();
      let layout = unsafe { Layout::from_size_align_unchecked(size, align) };

      unsafe { alloc::alloc::dealloc(self.mem.0, layout) };
    }
  }
}

pub mod internal {
  //! Unstable API exposing implementation details for tests and benchmarks.

  use super::*;

  pub fn num_slots<T>(t: &HashMapNZ64<T>) -> usize {
    t.internal_num_slots()
  }

  pub fn num_bytes<T>(t: &HashMapNZ64<T>) -> usize {
    t.internal_num_bytes()
  }

  pub fn load<T>(t: &HashMapNZ64<T>) -> f64 {
    t.internal_load()
  }

  pub fn allocation_info<T>(t: &HashMapNZ64<T>) -> Option<(NonNull<u8>, Layout)> {
    t.internal_allocation_info()
  }
}
