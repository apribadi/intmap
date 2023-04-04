use crate::prelude::*;

pub struct HashSetNZ64(HashMapNZ64<()>);

#[derive(Clone)]
pub struct Iter<'a>(map::Keys<'a, ()>);

impl<'a> FusedIterator for Iter<'a> {}
impl<'a> ExactSizeIterator for Iter<'a> {}

impl HashSetNZ64 {
  pub fn new() -> Self {
    Self(HashMapNZ64::new())
  }

  pub fn new_seeded(rng: &mut Rng) -> Self {
    Self(HashMapNZ64::new_seeded(rng))
  }

  pub fn len(&self) -> usize {
    self.0.len()
  }

  pub fn is_empty(&self) -> bool {
    self.0.is_empty()
  }

  pub fn contains(&self, key: NonZeroU64) -> bool {
    self.0.contains_key(key)
  }

  pub fn insert(&mut self, key: NonZeroU64) -> bool {
    self.0.insert(key, ()).is_some()
  }

  pub fn remove(&mut self, key: NonZeroU64) -> bool {
    self.0.remove(key).is_some()
  }

  pub fn clear(&mut self) {
    self.0.clear()
  }

  pub fn reset(&mut self) {
    self.0.reset()
  }

  pub fn iter(&self) -> Iter<'_> {
    Iter(self.0.keys())
  }
}

impl fmt::Debug for HashSetNZ64 {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
    let mut a = self.iter().collect::<Vec<_>>();

    a.sort();

    let mut f = f.debug_set();

    for key in a.iter() {
      let _: _ = f.entry(key);
    }

    f.finish()
  }
}

impl<'a> Iterator for Iter<'a> {
  type Item = NonZeroU64;

  fn next(&mut self) -> Option<Self::Item> {
    self.0.next()
  }

  fn size_hint(&self) -> (usize, Option<usize>) {
    self.0.size_hint()
  }
}
