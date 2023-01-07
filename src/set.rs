use crate::prelude::*;

pub struct HashSetNZ64(HashMapNZ64<()>);

impl HashSetNZ64 {
  pub fn new() -> Self {
    Self(HashMapNZ64::new())
  }

  #[inline]
  pub fn is_empty(&self) -> bool {
    self.0.is_empty()
  }

  #[inline]
  pub fn len(&self) -> usize {
    self.0.len()
  }

  #[inline]
  pub fn contains(&self, key: NonZeroU64) -> bool {
    self.0.contains_key(key)
  }

  #[inline]
  pub fn insert(&mut self, key: NonZeroU64) -> bool {
    self.0.insert(key, ()).is_some()
  }

  #[inline]
  pub fn remove(&mut self, key: NonZeroU64) -> bool {
    self.0.remove(key).is_some()
  }

  #[inline]
  pub fn clear(&mut self) {
    self.0.clear()
  }
}
