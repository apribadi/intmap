use crate::prelude::*;

pub trait BenchMap {
  fn new() -> Self;
  fn get(&self, key: NonZeroU64) -> Option<u64>;
  fn insert(&mut self, key: NonZeroU64, value: u64) -> Option<u64>;
  fn remove(&mut self, key: NonZeroU64) -> Option<u64>;
  fn heap_memory_in_bytes(&self) -> usize { 0 }
}

impl BenchMap for HashMapNZ64<u64> {
  #[inline]
  fn new() -> Self { HashMapNZ64::new() }

  #[inline]
  fn get(&self, key: NonZeroU64) -> Option<u64> { self.get(key).map(|x| *x) }

  #[inline]
  fn insert(&mut self, key: NonZeroU64, value: u64) -> Option<u64> { self.insert(key, value) }

  #[inline]
  fn remove(&mut self, key: NonZeroU64) -> Option<u64> { self.remove(key) }

  fn heap_memory_in_bytes(&self) -> usize {
    match wordmap::map::internal::allocation_info(self) {
      None => { 0 }
      Some(info) => info.1.size()
    }
  }
}

impl BenchMap for HashMap<NonZeroU64, u64> {
  #[inline]
  fn new() -> Self { HashMap::new() }

  #[inline]
  fn get(&self, key: NonZeroU64) -> Option<u64> { self.get(&key).map(|x| *x) }

  #[inline]
  fn insert(&mut self, key: NonZeroU64, value: u64) -> Option<u64> { self.insert(key, value) }

  #[inline]
  fn remove(&mut self, key: NonZeroU64) -> Option<u64> { self.remove(&key) }
}

impl BenchMap for AHashMap<NonZeroU64, u64> {
  #[inline]
  fn new() -> Self { AHashMap::new() }

  #[inline]
  fn get(&self, key: NonZeroU64) -> Option<u64> { self.get(&key).map(|x| *x) }

  #[inline]
  fn insert(&mut self, key: NonZeroU64, value: u64) -> Option<u64> { self.insert(key, value) }

  #[inline]
  fn remove(&mut self, key: NonZeroU64) -> Option<u64> { self.remove(&key) }
}

impl BenchMap for FxHashMap<NonZeroU64, u64> {
  #[inline]
  fn new() -> Self { FxHashMap::default() }

  #[inline]
  fn get(&self, key: NonZeroU64) -> Option<u64> { self.get(&key).map(|x| *x) }

  #[inline]
  fn insert(&mut self, key: NonZeroU64, value: u64) -> Option<u64> { self.insert(key, value) }

  #[inline]
  fn remove(&mut self, key: NonZeroU64) -> Option<u64> { self.remove(&key) }
}

impl BenchMap for IntMap<u64> {
  #[inline]
  fn new() -> Self { IntMap::new() }

  #[inline]
  fn get(&self, key: NonZeroU64) -> Option<u64> { self.get(key.get()).map(|x| *x) }

  #[inline]
  fn insert(&mut self, key: NonZeroU64, value: u64) -> Option<u64> { self.insert(key.get(), value) }

  #[inline]
  fn remove(&mut self, key: NonZeroU64) -> Option<u64> { self.remove(key.get()) }
}

pub struct FakeMap(u64);

impl BenchMap for FakeMap {
  #[inline]
  fn new() -> Self {
    Self(0)
  }

  #[inline]
  fn get(&self, key: NonZeroU64) -> Option<u64> {
    Some(self.0.wrapping_add(u64::from(key)))
  }

  #[inline]
  fn insert(&mut self, key: NonZeroU64, value: u64) -> Option<u64> {
    let x = self.0.wrapping_add(u64::from(key)).wrapping_add(value);
    self.0 = x;
    Some(x)
  }

  #[inline]
  fn remove(&mut self, key: NonZeroU64) -> Option<u64> {
    let x = self.0.wrapping_add(u64::from(key));
    self.0 = x;
    Some(x)
  }
}
