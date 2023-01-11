mod prelude;
mod rng;
pub mod map;
pub mod set;

use core::num::NonZeroU64;
use map::HashMapNZ64;
use rng::Rng;
use set::HashSetNZ64;
use std::collections::HashMap;

pub fn std_contains_key(t: &HashMap<NonZeroU64, u64>, x: NonZeroU64) -> bool {
  t.contains_key(&x)
}

pub fn std_remove(t: &mut HashMap<NonZeroU64, u64>, x: NonZeroU64) -> Option<u64> {
  t.remove(&x)
}

pub fn mnz_len(t: &HashMapNZ64<u64>) -> usize {
  t.len()
}

pub fn mnz_is_empty(t: &HashMapNZ64<u64>) -> bool {
  t.is_empty()
}

pub fn mnz_contains_key(t: &HashMapNZ64<u64>, x: NonZeroU64) -> bool {
  t.contains_key(x)
}

pub fn mnz_contains_key_x2(t: &HashMapNZ64<u64>, x: NonZeroU64, y: NonZeroU64) -> bool {
  t.contains_key(x) & t.contains_key(y)
}

pub fn mnz_get(t: &HashMapNZ64<u64>, x: NonZeroU64) -> Option<&u64> {
  t.get(x)
}

pub fn mnz_insert(t: &mut HashMapNZ64<u64>, x: NonZeroU64, v: u64) -> Option<u64> {
  t.insert(x, v)
}

pub fn mnz_remove(t: &mut HashMapNZ64<u64>, x: NonZeroU64) -> Option<u64> {
  t.remove(x)
}

pub fn mnz_clear(t: &mut HashMapNZ64<u64>) {
  t.clear()
}

pub fn snz_contains(t: &HashSetNZ64, x: NonZeroU64) -> bool {
  t.contains(x)
}

pub fn foo(g: &mut Rng) -> [u64; 2] {
  [ g.u64(), g.u64() ]
}

/*
use ahash::AHashMap;
use fxhash::FxHashMap;

pub fn ah_contains_key(t: &AHashMap<NonZeroU64, u64>, x: NonZeroU64) -> bool {
  t.contains_key(&x)
}

pub fn fx_contains_key(t: &FxHashMap<NonZeroU64, u64>, x: NonZeroU64) -> bool {
  t.contains_key(&x)
}

*/
