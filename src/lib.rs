//! This crate implements a fast hash map and hash set keyed by `NonZeroU64`s.

mod prelude;
pub mod map;
pub mod rng;
pub mod set;
pub mod two;
pub mod ptr;

pub fn u64_get(t: &map::HashMapNZ64<u64>, key: core::num::NonZeroU64) -> Option<&u64> {
  t.get(key)
}

pub fn u64_get_value(t: &map::HashMapNZ64<u64>, key: core::num::NonZeroU64) -> Option<u64> {
  match t.get(key) {
    None => { None }
    Some(&value) => { Some(value) }
  }
}

pub fn u64_contains_key(t: &map::HashMapNZ64<u64>, key: core::num::NonZeroU64) -> bool {
  t.contains_key(key)
}

pub fn u64_contains_key2(t: &map::HashMapNZ64<u64>, key: core::num::NonZeroU64) -> bool {
  t.get(key).is_some()
}

pub fn u64_insert(t: &mut map::HashMapNZ64<u64>, key: core::num::NonZeroU64, value: u64) -> Option<u64> {
  t.insert(key, value)
}

pub fn u64_remove(t: &mut map::HashMapNZ64<u64>, key: core::num::NonZeroU64) -> Option<u64> {
  t.remove(key)
}

