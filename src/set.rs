use crate::prelude::*;

pub struct HashSetNZ64(HashMapNZ64<()>);

impl HashSetNZ64 {
  #[inline]
  pub fn new() -> Self {
    Self(HashMapNZ64::new())
  }

  #[inline]
  pub fn new_seeded(rng: &mut Rng) -> Self {
    Self(HashMapNZ64::new_seeded(rng))
  }

  #[inline]
  pub fn len(&self) -> usize {
    self.0.len()
  }

  #[inline]
  pub fn is_empty(&self) -> bool {
    self.0.is_empty()
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
  pub fn reset(&mut self) {
    self.0.reset()
  }

  #[inline]
  pub fn sorted(&self) -> Box<[NonZeroU64]> {
    self.0.sorted_keys()
  }
}

impl fmt::Debug for HashSetNZ64 {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
    let mut f = f.debug_set();

    for key in self.sorted().iter() {
      f.entry(key);
    }

    f.finish()
  }
}
