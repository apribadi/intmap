mod prelude;
mod rng;
pub mod map;
pub mod set;

use core::num::NonZeroU64;
use map::HashMapNZ64;
use std::collections::HashMap;

pub fn std_contains_key(t: &HashMap<NonZeroU64, u64>, x: NonZeroU64) -> bool {
  t.contains_key(&x)
}

pub fn std_get(t: &HashMap<NonZeroU64, u64>, x: NonZeroU64) -> Option<&u64> {
  t.get(&x)
}

pub fn nz_contains_key(t: &HashMapNZ64<u64>, x: NonZeroU64) -> bool {
  t.contains_key(x)
}

pub fn nz_contains_key_x2(t: &HashMapNZ64<u64>, x: NonZeroU64, y: NonZeroU64) -> bool {
  t.contains_key(x) && t.contains_key(y)
}

pub fn nz_get(t: &HashMapNZ64<u64>, x: NonZeroU64) -> Option<&u64> {
  t.get(x)
}

pub fn nz_insert(t: &mut HashMapNZ64<u64>, x: NonZeroU64, v: u64) -> Option<u64> {
  t.insert(x, v)
}

pub fn nz_remove(t: &mut HashMapNZ64<u64>, x: NonZeroU64) -> Option<u64> {
  t.remove(x)
}
