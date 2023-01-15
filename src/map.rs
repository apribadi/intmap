//! This module implements a fast hash map keyed by `NonZeroU64`s.
//!
//! blah blah blah
//!
//! blah blah blah
//!
//! design discussion

use crate::prelude::*;

/// A fast hash map keyed by `NonZeroU64`s.
///
/// The module documentation [`wordmap::map`](crate::map) discusses the design
/// tradeoffs of this data structure.

pub struct HashMapNZ64<A> {
  mixer: Mixer,
  table: *const Slot<A>, // covariant in `A`
  shift: usize,
  space: usize,
  check: *const Slot<A>,
}

unsafe impl<A: Send> Send for HashMapNZ64<A> {}
unsafe impl<A: Sync> Sync for HashMapNZ64<A> {}

#[derive(Clone, Copy)]
struct Mixer(u64, u64);

struct Slot<A> {
  hash: u64,
  value: MaybeUninit<A>,
}

/*
pub enum Entry<'a, A: 'a> {
  Vacant(VacantEntry<'a, A>),
  Occupied(OccupiedEntry<'a, A>),
}

pub struct VacantEntry<'a, A: 'a> {
  hashmap: &'a mut HashMapNZ64<A>,
  slot: *mut Slot<A>,
  variance: PhantomData<&'a mut A>,
}

pub struct OccupiedEntry<'a, A: 'a> {
  slot: *mut Slot<A>,
  variance: PhantomData<&'a mut A>,
}
*/

#[derive(Clone)]
pub struct Iter<'a, A: 'a> {
  mixer: Mixer,
  len: usize,
  ptr: *const Slot<A>,
  variance: PhantomData<&'a A>,
}

pub struct IterMut<'a, A: 'a> {
  mixer: Mixer,
  len: usize,
  ptr: *mut Slot<A>,
  variance: PhantomData<&'a mut A>,
}

#[derive(Clone)]
pub struct Keys<'a, A: 'a> {
  mixer: Mixer,
  len: usize,
  ptr: *const Slot<A>,
  variance: PhantomData<&'a A>,
}

#[derive(Clone)]
pub struct Values<'a, A: 'a> {
  len: usize,
  ptr: *const Slot<A>,
  variance: PhantomData<&'a A>,
}

pub struct ValuesMut<'a, A: 'a> {
  len: usize,
  ptr: *mut Slot<A>,
  variance: PhantomData<&'a mut A>,
}

impl<'a, A> FusedIterator for Iter<'a, A> {}
impl<'a, A> FusedIterator for IterMut<'a, A> {}
impl<'a, A> FusedIterator for Keys<'a, A> {}
impl<'a, A> FusedIterator for Values<'a, A> {}
impl<'a, A> FusedIterator for ValuesMut<'a, A> {}

impl<'a, A> ExactSizeIterator for Iter<'a, A> {}
impl<'a, A> ExactSizeIterator for IterMut<'a, A> {}
impl<'a, A> ExactSizeIterator for Keys<'a, A> {}
impl<'a, A> ExactSizeIterator for Values<'a, A> {}
impl<'a, A> ExactSizeIterator for ValuesMut<'a, A> {}

const INITIAL_U: usize = 4;
const INITIAL_V: usize = 3;
const INITIAL_D: usize = 1 << INITIAL_U;
const INITIAL_E: usize = 1 << INITIAL_V;
const INITIAL_N: usize = INITIAL_D + INITIAL_E;
const INITIAL_S: usize = 64 - INITIAL_U;
const INITIAL_R: usize = INITIAL_D / 2;

#[inline(always)]
const unsafe fn spot(shift: usize, h: u64) -> isize {
  if ! (shift <= 63) { unsafe { unreachable_unchecked() }; }
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
  const fn new(m: u64) -> Self {
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

impl<A> HashMapNZ64<A> {
  /// Creates an empty map, seeding the hash mixer from a thread-local random
  /// number generator.

  #[inline]
  pub fn new() -> Self {
    Self {
      mixer: Mixer::new(rng::thread_local::u64()),
      table: ptr::null(),
      shift: INITIAL_S,
      space: INITIAL_R,
      check: ptr::null(),
    }
  }

  /// Creates an empty map, seeding the hash mixer from the given random number
  /// generator.

  #[inline]
  pub fn new_seeded(rng: &mut Rng) -> Self {
    Self {
      mixer: Mixer::new(rng.u64()),
      table: ptr::null(),
      shift: INITIAL_S,
      space: INITIAL_R,
      check: ptr::null(),
    }
  }

  /// Returns the number of items.

  #[inline]
  pub fn len(&self) -> usize {
    let s = self.shift;
    let r = self.space;
    let c = 1 << (64 - s - 1);
    let k = c - r;
    k
  }

  /// Returns whether the map contains zero items.

  #[inline]
  pub fn is_empty(&self) -> bool {
    self.len() == 0
  }

  /// Returns whether the map contains the given key.

  #[inline]
  pub fn contains_key(&self, key: NonZeroU64) -> bool {
    let t = self.table;

    if t.is_null() { return false; }

    let m = self.mixer;
    let s = self.shift;
    let h = u64::from(m.hash(key));

    let mut p = unsafe { t.offset(- spot(s, h)) };
    let mut x = unsafe { &*p }.hash;

    while x > h {
      p = unsafe { p.add(1) };
      x = unsafe { &*p }.hash;
    }

    return x == h;
  }

  /// Returns a reference to the value associated with the given key, if
  /// present.

  #[inline]
  pub fn get(&self, key: NonZeroU64) -> Option<&A> {
    let t = self.table;

    if t.is_null() { return None; }

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

  #[inline]
  pub fn get_mut(&mut self, key: NonZeroU64) -> Option<&mut A> {
    let t = self.table as *mut Slot<A>;

    if t.is_null() { return None; }

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

  /// Inserts the given key and value into the map. Returns the previous value
  /// associated with given key, if one was present.
  ///
  /// # Panics
  ///
  /// Panics when allocation fails. If that happens, it is possible for the map
  /// to leak an arbitrary set of items, but the map will remain in a valid
  /// state.

  #[inline]
  pub fn insert(&mut self, key: NonZeroU64, value: A) -> Option<A> {
    let t = self.table as *mut Slot<A>;

    if t.is_null() {
      self.insert_cold_init_table(key, value);
      return None;
    }

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
    let b = self.check;

    if r == 0 || ptr::eq(p, b) { self.insert_cold_grow_table(); }

    None
  }

  #[inline(never)]
  #[cold]
  fn insert_cold_init_table(&mut self, key: NonZeroU64, value: A) {
    assert!(INITIAL_N <= isize::MAX as usize / mem::size_of::<Slot<A>>());

    let align = mem::align_of::<Slot<A>>();
    let size = INITIAL_N * mem::size_of::<Slot<A>>();

    let layout = unsafe { Layout::from_size_align_unchecked(size, align) };

    let a = unsafe { std::alloc::alloc_zeroed(layout) } as *mut Slot<A>;

    if a.is_null() { match std::alloc::handle_alloc_error(layout) {} }

    let t = unsafe { a.add(INITIAL_D - 1) };
    let b = unsafe { a.add(INITIAL_N - 1) };

    let m = self.mixer;
    let h = u64::from(m.hash(key));
    let p = unsafe { t.offset(- spot(INITIAL_S, h)) };

    unsafe { &mut *p }.hash = h;
    unsafe { &mut *p }.value = MaybeUninit::new(value);

    // We don't modify the table until after we know that allocation won't fail.

    self.table = t;
    self.space = INITIAL_R - 1;
    self.check = b;
  }

  #[inline(never)]
  #[cold]
  fn insert_cold_grow_table(&mut self) {
    // TODO:
    //
    // Preserve invariants even if an assertion fails.
    //
    // If the `check` spot is occupied, temporarily remove the item there, then replace it at the
    // end.

    let old_t = self.table as *mut Slot<A>;
    let old_s = self.shift;
    let old_r = self.space;
    let old_b = self.check;

    // d = 2 ** u
    // e = 2 ** v
    // n = d + e
    //
    // t = a + (d - 1)
    // b = a + (n - 1)

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

    assert!(new_u <= usize::BITS as usize - 1 && new_u <= 64);
    assert!(new_v <= usize::BITS as usize - 2);

    let new_s = 64 - new_u;
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
        let v = unsafe { (&*p).value.assume_init_read() };
        j = max(j, (! x >> new_s) as usize);
        let q = unsafe { new_a.add(j) };
        unsafe { &mut *q }.hash = x;
        unsafe { &mut *q }.value = MaybeUninit::new(v);
        j = j + 1;
      }
    });

    self.table = new_t;
    self.shift = new_s;
    self.space = new_r;
    self.check = new_b;

    unsafe { std::alloc::dealloc(old_a as *mut u8, old_layout) };
  }

  /// Removes the given key from the map. Returns the previous value associated
  /// with the given key, if one was present.

  #[inline]
  pub fn remove(&mut self, key: NonZeroU64) -> Option<A> {
    let t = self.table as *mut Slot<A>;

    if t.is_null() { return None; }

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

      if p < unsafe { t.offset(- spot(s, x)) } || /* unlikely */ x == 0 { break; }

      unsafe { &mut *p }.hash = x;
      unsafe { &mut *p }.value = MaybeUninit::new(unsafe { (&*q).value.assume_init_read() });

      p = q;
    }

    unsafe { &mut *p }.hash = 0;

    self.space = self.space + 1;

    Some(v)
  }

  /*
  #[inline]
  pub fn entry(&mut self, key: NonZeroU64) -> Entry<'_, A> {
    let t = self.table as *mut Slot<A>;

    if t.is_null() { 
      unimplemented!()
    }

    let m = self.mixer;
    let s = self.shift;
    let h = u64::from(m.hash(key));

    let mut p = unsafe { t.offset(- spot(s, h)) };
    let mut x = unsafe { &*p }.hash;

    while x > h {
      p = unsafe { p.add(1) };
      x = unsafe { &*p }.hash;
    }

    if x != h {
      Entry::Vacant(VacantEntry {
        hashmap: self,
        slot: p,
        variance: PhantomData,
      })
    } else {
      Entry::Occupied(OccupiedEntry {
        slot: p,
        variance: PhantomData,
      })
    }
  }
  */

  /// Removes every item from the map. Retains heap-allocated memory.

  #[inline]
  pub fn clear(&mut self) {
    let t = self.table as *mut Slot<A>;

    if t.is_null() { return; }

    let s = self.shift;
    let r = self.space;
    let b = self.check as *mut Slot<A>;
    let c = 1 << (64 - s - 1);
    let k = c - r;

    if k == 0 { return; }

    if mem::needs_drop::<A>() {
      // WARNING!
      //
      // This loop must be careful to leave the map in a valid state even if a
      // call to `drop` panics. In particular, because we traverse the table in
      // reverse order, we ensure that we don't remove an item that is
      // currently displacing another item.

      let mut p = b;
      let mut k = k;
      let mut r = r;

      loop {
        p = unsafe { p.sub(1) };

        if unsafe { &mut *p }.hash != 0 {
          unsafe { &mut *p }.hash = 0;
          k = k - 1;
          r = r + 1;
          self.space = r;
          unsafe { (&mut *p).value.assume_init_drop() };
          if k == 0 { break; }
        }
      }
    } else {
      let d = 1 << (64 - s);
      let a = unsafe { t.sub(d - 1) };

      each_mut(a, b, |p| { unsafe { &mut *p }.hash = 0; });

      self.space = c;
    }
  }

  /// Removes every item from the map. Releases heap-allocated memory.

  #[inline]
  pub fn reset(&mut self) {
    let t = self.table as *mut Slot<A>;

    if t.is_null() { return; }

    let s = self.shift;
    let b = self.check;
    let d = 1 << (64 - s);
    let e = unsafe { b.offset_from(t) } as usize;
    let n = d + e;
    let a = unsafe { t.sub(d - 1) };

    // If we're in `Self::drop` and `self` has been subject to scalar
    // replacement of aggregates, then the following are all dead stores and
    // should be optimized away.

    self.table = ptr::null();
    self.shift = INITIAL_S;
    self.space = INITIAL_R;
    self.check = ptr::null();

    if mem::needs_drop::<A>() {
      // We have already placed `self` into a valid configuration, so if
      // `A::drop` panics we can just leak the table.

      each_mut(a, b, |p| {
        if unsafe { &mut *p }.hash != 0 {
          unsafe { (&mut *p).value.assume_init_drop() };
        }
      })
    }

    let align = mem::align_of::<Slot<A>>();
    let size = n * mem::size_of::<Slot<A>>();
    let layout = unsafe { Layout::from_size_align_unchecked(size, align) };

    unsafe { std::alloc::dealloc(a as *mut u8, layout) };
  }

  /// Returns an iterator yielding each key and a reference to its associated
  /// value. The iterator item type is `(NonZeroU64, &'_ A)`.

  #[inline]
  pub fn iter(&self) -> Iter<'_, A> {
    let m = self.mixer;
    let s = self.shift;
    let r = self.space;
    let b = self.check;
    let c = 1 << (64 - s - 1);
    let k = c - r;

    Iter { mixer: m, len: k, ptr: b, variance: PhantomData }
  }

  /// Returns an iterator yielding each key and a mutable reference to its
  /// associated value. The iterator item type is `(NonZeroU64, &'_ mut A)`.

  #[inline]
  pub fn iter_mut(&mut self) -> IterMut<'_, A> {
    let m = self.mixer;
    let t = self.table as *mut Slot<A>;
    let s = self.shift;
    let r = self.space;
    let c = 1 << (64 - s - 1);
    let d = 1 << (64 - s);
    let k = c - r;
    let p = if t.is_null() { ptr::null_mut() } else { unsafe { t.sub(d - 1) } };

    IterMut { mixer: m, len: k, ptr: p, variance: PhantomData }
  }

  /// Returns an iterator yielding each key. The iterator item type is
  /// `NonZeroU64`.

  #[inline]
  pub fn keys(&self) -> Keys<'_, A> {
    let m = self.mixer;
    let t = self.table;
    let s = self.shift;
    let r = self.space;
    let c = 1 << (64 - s - 1);
    let d = 1 << (64 - s);
    let k = c - r;
    let p = if t.is_null() { ptr::null() } else { unsafe { t.sub(d - 1) } };

    Keys { mixer: m, len: k, ptr: p, variance: PhantomData }
  }

  /// Returns an iterator yielding a reference to each value. The iterator item
  /// type is `&'_ A`.

  #[inline]
  pub fn values(&self) -> Values<'_, A> {
    let t = self.table;
    let s = self.shift;
    let r = self.space;
    let c = 1 << (64 - s - 1);
    let d = 1 << (64 - s);
    let k = c - r;
    let p = if t.is_null() { ptr::null() } else { unsafe { t.sub(d - 1) } };

    Values { len: k, ptr: p, variance: PhantomData }
  }

  /// Returns an iterator yielding a mutable reference to each value. The
  /// iterator item type is `&'_ mut A`.

  #[inline]
  pub fn values_mut(&mut self) -> ValuesMut<'_, A> {
    let t = self.table as *mut Slot<A>;
    let s = self.shift;
    let r = self.space;
    let c = 1 << (64 - s - 1);
    let d = 1 << (64 - s);
    let k = c - r;
    let p = if t.is_null() { ptr::null_mut() } else { unsafe { t.sub(d - 1) } };

    ValuesMut { len: k, ptr: p, variance: PhantomData }
  }

  #[inline]
  fn internal_num_slots(&self) -> usize {
    let t = self.table;

    if t.is_null() { return 0; }

    let s = self.shift;
    let b = self.check;
    let d = 1 << (64 - s);
    let e = unsafe { b.offset_from(t) } as usize;
    let n = d + e;
    n
  }

  #[inline]
  fn internal_num_bytes(&self) -> usize {
    self.internal_num_slots() * mem::size_of::<Slot<A>>()
  }

  #[inline]
  fn internal_load(&self) -> f64 {
    let k = self.len();
    let n = self.internal_num_slots();

    if n == 0 { return 0.; }

    (k as f64) / (n as f64) 
  }

  #[inline]
  fn internal_allocation_info(&self) -> Option<(NonNull<u8>, Layout)> {
    let t = self.table;

    if t.is_null() { return None; }

    let s = self.shift;
    let b = self.check;
    let d = 1 << (64 - s);
    let e = unsafe { b.offset_from(t) } as usize;
    let n = d + e;
    let a = unsafe { t.sub(d - 1) };

    let align = mem::align_of::<Slot<A>>();
    let size = n * mem::size_of::<Slot<A>>();
    let layout = unsafe { Layout::from_size_align_unchecked(size, align) };

    Some((unsafe { NonNull::new_unchecked(a as *mut u8) }, layout))
  }
}

impl<A> Drop for HashMapNZ64<A> {
  #[inline]
  fn drop(&mut self) {
    self.reset()
  }
}

impl<A> Index<NonZeroU64> for HashMapNZ64<A> {
  type Output = A;

  #[inline]
  fn index(&self, key: NonZeroU64) -> &A {
    self.get(key).unwrap()
  }
}

impl<A> IndexMut<NonZeroU64> for HashMapNZ64<A> {
  #[inline]
  fn index_mut(&mut self, key: NonZeroU64) -> &mut A {
    self.get_mut(key).unwrap()
  }
}

impl<A: fmt::Debug> fmt::Debug for HashMapNZ64<A> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
    let mut items = self.iter().collect::<Vec<(NonZeroU64, &A)>>();

    items.sort_by_key(|x| x.0);

    let mut f = f.debug_map();

    for (key, value) in items.iter() {
      f.entry(key, value);
    }

    f.finish()
  }
}

/*
impl<'a, A> OccupiedEntry<'a, A> {
  pub fn value_mut(&mut self) -> &mut A {
    unsafe { (&mut *self.slot).value.assume_init_mut() }
  }

  pub fn into_value_mut(self) -> &'a mut A {
    unsafe { (&mut *self.slot).value.assume_init_mut() }
  }

  pub fn replace(&mut self, value: A) -> A {
    mem::replace(self.value_mut(), value)
  }

  pub fn remove(self) -> A {
    unimplemented!()
  }
}
*/

impl<'a, A> Iterator for Iter<'a, A> {
  type Item = (NonZeroU64, &'a A);

  #[inline]
  fn next(&mut self) -> Option<Self::Item> {
    let k = self.len;

    if k == 0 { return None; }

    let mut p = unsafe { self.ptr.sub(1) };
    let mut x = unsafe { &*p }.hash;

    while x == 0 {
      p = unsafe { p.sub(1) };
      x = unsafe { &*p }.hash;
    }

    let m = self.mixer;
    let x = m.hash(unsafe { NonZeroU64::new_unchecked(x) });
    let v = unsafe { (&*p).value.assume_init_ref() };

    self.ptr = p;
    self.len = k - 1;

    Some((x, v))
  }

  #[inline]
  fn size_hint(&self) -> (usize, Option<usize>) {
    (self.len, Some(self.len))
  }
}

impl<'a, A> Iterator for IterMut<'a, A> {
  type Item = (NonZeroU64, &'a mut A);

  #[inline]
  fn next(&mut self) -> Option<Self::Item> {
    let k = self.len;

    if k == 0 { return None; }

    let mut p = self.ptr;
    let mut x = unsafe { &*p }.hash;

    while x == 0 {
      p = unsafe { p.add(1) };
      x = unsafe { &*p }.hash;
    }

    let m = self.mixer;
    let x = m.hash(unsafe { NonZeroU64::new_unchecked(x) });
    let v = unsafe { (&mut *p).value.assume_init_mut() };

    self.ptr = unsafe { p.add(1) };
    self.len = k - 1;

    Some((x, v))
  }

  #[inline]
  fn size_hint(&self) -> (usize, Option<usize>) {
    (self.len, Some(self.len))
  }
}

impl<'a, A> Iterator for Keys<'a, A> {
  type Item = NonZeroU64;

  #[inline]
  fn next(&mut self) -> Option<Self::Item> {
    let k = self.len;

    if k == 0 { return None; }

    let mut p = self.ptr;
    let mut x = unsafe { &*p }.hash;

    while x == 0 {
      p = unsafe { p.add(1) };
      x = unsafe { &*p }.hash;
    }

    let m = self.mixer;
    let x = m.hash(unsafe { NonZeroU64::new_unchecked(x) });

    self.ptr = unsafe { p.add(1) };
    self.len = k - 1;

    Some(x)
  }

  #[inline]
  fn size_hint(&self) -> (usize, Option<usize>) {
    (self.len, Some(self.len))
  }
}

impl<'a, A> Iterator for Values<'a, A> {
  type Item = &'a A;

  #[inline]
  fn next(&mut self) -> Option<Self::Item> {
    let k = self.len;

    if k == 0 { return None; }

    let mut p = self.ptr;
    let mut x = unsafe { &*p }.hash;

    while x == 0 {
      p = unsafe { p.add(1) };
      x = unsafe { &*p }.hash;
    }

    let v = unsafe { (&*p).value.assume_init_ref() };

    self.ptr = unsafe { p.add(1) };
    self.len = k - 1;

    Some(v)
  }

  #[inline]
  fn size_hint(&self) -> (usize, Option<usize>) {
    (self.len, Some(self.len))
  }
}

impl<'a, A> Iterator for ValuesMut<'a, A> {
  type Item = &'a mut A;

  #[inline]
  fn next(&mut self) -> Option<Self::Item> {
    let k = self.len;

    if k == 0 { return None; }

    let mut p = self.ptr;
    let mut x = unsafe { &*p }.hash;

    while x == 0 {
      p = unsafe { p.add(1) };
      x = unsafe { &*p }.hash;
    }

    let v = unsafe { (&mut *p).value.assume_init_mut() };

    self.ptr = unsafe { p.add(1) };
    self.len = k - 1;

    Some(v)
  }

  #[inline]
  fn size_hint(&self) -> (usize, Option<usize>) {
    (self.len, Some(self.len))
  }
}

pub mod internal {
  //! This unstable API exposes internal implementation details for tests and benchmarks.

  use crate::prelude::*;

  #[inline]
  pub fn num_slots<A>(t: &HashMapNZ64<A>) -> usize {
    t.internal_num_slots()
  }

  #[inline]
  pub fn num_bytes<A>(t: &HashMapNZ64<A>) -> usize {
    t.internal_num_bytes()
  }

  #[inline]
  pub fn load<A>(t: &HashMapNZ64<A>) -> f64 {
    t.internal_load()
  }

  #[inline]
  pub fn allocation_info<A>(t: &HashMapNZ64<A>) -> Option<(NonNull<u8>, Layout)> {
    t.internal_allocation_info()
  }
}
