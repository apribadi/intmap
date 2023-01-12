use crate::prelude::*;

pub struct HashSetNZ64(HashMapNZ64<()>);

impl HashSetNZ64 {
  #[inline]
  pub fn new() -> Self {
    Self(HashMapNZ64::new())
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

  #[inline]
  pub fn sorted_keys(&self) -> Box<[NonZeroU64]> {
    self.0.sorted_keys()
  }
}

impl fmt::Debug for HashSetNZ64 {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
    let mut f = f.debug_set();

    for key in self.sorted_keys().iter() {
      f.entry(key);
    }

    f.finish()
  }
}
