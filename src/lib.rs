//! This crate implements a fast hash map and hash set keyed by `NonZeroU64`s.

#![deny(unsafe_op_in_unsafe_fn)]
#![warn(elided_lifetimes_in_paths)]
#![warn(trivial_casts)]
#![warn(trivial_numeric_casts)]
#![warn(unused_lifetimes)]
#![warn(unused_qualifications)]

mod prelude;
pub mod map;
pub mod rng;
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

pub fn std_insert(t: &mut HashMap<NonZeroU64, u64>, x: NonZeroU64, y: u64) -> Option<u64> {
  t.insert(x, y)
}

pub fn std_remove(t: &mut HashMap<NonZeroU64, u64>, x: NonZeroU64) -> Option<u64> {
  t.remove(&x)
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

pub fn nz_iter(t: &HashMapNZ64<u64>) -> map::Iter<'_, u64> {
  t.iter()
}

pub fn nz_clear(t: &mut HashMapNZ64<u64>) {
  t.clear()
}

pub fn nz_reset(t: &mut HashMapNZ64<u64>) {
  t.reset()
}
