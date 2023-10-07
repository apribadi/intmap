//! This crate implements a fast hash map and hash set keyed by `NonZeroU64`s.

#![deny(unsafe_op_in_unsafe_fn)]
#![warn(elided_lifetimes_in_paths)]
#![warn(non_ascii_idents)]
#![warn(trivial_numeric_casts)]
#![warn(unreachable_pub)]
#![warn(unused_lifetimes)]
#![warn(unused_qualifications)]
#![warn(unused_results)]

mod prelude;
pub mod map;
pub mod rng;
pub mod set;

pub fn get(t: &map::HashMapNZ64<u64>, key: core::num::NonZeroU64) -> Option<&u64> {
  t.get(key)
}

pub fn insert(t: &mut map::HashMapNZ64<u64>, key: core::num::NonZeroU64, value: u64) -> Option<u64> {
  t.insert(key, value)
}

pub fn remove(t: &mut map::HashMapNZ64<u64>, key: core::num::NonZeroU64) -> Option<u64> {
  t.remove(key)
}

