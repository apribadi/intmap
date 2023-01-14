use crate::prelude::*;

pub trait BenchMap {
  fn make() -> Self;
  fn get(&self, key: NonZeroU64) -> Option<u64>;
  fn insert(&mut self, key: NonZeroU64, value: u64) -> Option<u64>;
  fn remove(&mut self, key: NonZeroU64) -> Option<u64>;
}

impl BenchMap for HashMapNZ64<u64> {
  #[inline]
  fn make() -> Self { HashMapNZ64::new() }

  #[inline]
  fn get(&self, key: NonZeroU64) -> Option<u64> { self.get(key).map(|x| *x) }

  #[inline]
  fn insert(&mut self, key: NonZeroU64, value: u64) -> Option<u64> { self.insert(key, value) }

  #[inline]
  fn remove(&mut self, key: NonZeroU64) -> Option<u64> { self.remove(key) }
}

impl BenchMap for HashMap<NonZeroU64, u64> {
  #[inline]
  fn make() -> Self { HashMap::new() }

  #[inline]
  fn get(&self, key: NonZeroU64) -> Option<u64> { self.get(&key).map(|x| *x) }

  #[inline]
  fn insert(&mut self, key: NonZeroU64, value: u64) -> Option<u64> { self.insert(key, value) }

  #[inline]
  fn remove(&mut self, key: NonZeroU64) -> Option<u64> { self.remove(&key) }
}

impl BenchMap for AHashMap<NonZeroU64, u64> {
  #[inline]
  fn make() -> Self { AHashMap::new() }

  #[inline]
  fn get(&self, key: NonZeroU64) -> Option<u64> { self.get(&key).map(|x| *x) }

  #[inline]
  fn insert(&mut self, key: NonZeroU64, value: u64) -> Option<u64> { self.insert(key, value) }

  #[inline]
  fn remove(&mut self, key: NonZeroU64) -> Option<u64> { self.remove(&key) }
}

impl BenchMap for FxHashMap<NonZeroU64, u64> {
  #[inline]
  fn make() -> Self { FxHashMap::default() }

  #[inline]
  fn get(&self, key: NonZeroU64) -> Option<u64> { self.get(&key).map(|x| *x) }

  #[inline]
  fn insert(&mut self, key: NonZeroU64, value: u64) -> Option<u64> { self.insert(key, value) }

  #[inline]
  fn remove(&mut self, key: NonZeroU64) -> Option<u64> { self.remove(&key) }
}

pub struct FakeMap(u64);

impl BenchMap for FakeMap {
  #[inline]
  fn make() -> Self {
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
