mod prelude;
mod rng;
pub mod hashmapnz64;

pub fn foo(t: &hashmapnz64::HashMapNZ64<u64>, x: core::num::NonZeroU64) -> bool {
  t.contains_key(x)
}

pub fn bar(t: &hashmapnz64::HashMapNZ64<u64>, x: core::num::NonZeroU64) -> Option<&u64> {
  t.get(x)
}
