use crate::prelude::*;

#[derive(Clone)]
pub struct Rng(NonZeroU128);

#[inline(always)]
const fn umulh(x: u64, y: u64) -> u64 {
  (((x as u128) * (y as u128)) >> 64) as u64
}

impl Rng {
  #[inline(always)]
  pub const fn new(state: NonZeroU128) -> Self {
    Self(state)
  }

  #[inline(always)]
  pub const fn from_seed(seed: [u8; 16]) -> Self {
    let s = u128::from_le_bytes(seed).saturating_add(1);
    Self::new(unsafe { NonZeroU128::new_unchecked(s) })
  }

  #[inline(always)]
  pub const fn from_hash(n: u128) -> Self {
    const M: u128 = 0x9670_4a6b_b5d2_c4fb_3aa6_45df_0540_268d;
    let n = n.wrapping_mul(M);
    let n = n.saturating_add(1);
    let n = n.swap_bytes();
    let n = n.wrapping_mul(M);
    let n = n.swap_bytes();
    let n = n.wrapping_mul(M);
    Self::new(unsafe { NonZeroU128::new_unchecked(n) })
  }

  pub fn from_entropy() -> Self {
    let mut seed = [0; 16];
    getrandom::getrandom(&mut seed).expect("getrandom::getrandom failed!");
    Self::from_seed(seed)
  }

  #[inline(always)]
  pub const fn state(&self) -> NonZeroU128 {
    self.0
  }

  #[inline(always)]
  pub fn split(&mut self) -> Self {
    let x = self.u64();
    let y = self.u64();
    let s = (x as u128) | ((y as u128) << 64);
    let s = s.saturating_add(1);
    let s = unsafe { NonZeroU128::new_unchecked(s) };
    Self::new(s)
  }

  #[inline(always)]
  pub fn u64(&mut self) -> u64 {
    const M: u64 = 0x9e37_79b9_7f4a_7c15;
    let s = self.0;
    let s = s.get();
    let a = s as u64;
    let b = (s >> 64) as u64;
    let c = a.rotate_right(7) ^ b;
    let d = a ^ a >> 19;
    let x = a ^ b.wrapping_mul(M).wrapping_add(umulh(b, M));
    let s = (c as u128) | ((d as u128) << 64);
    let s = unsafe { NonZeroU128::new_unchecked(s) };
    self.0 = s;
    x
  }

  #[inline(always)]
  pub fn i64(&mut self) -> i64 {
    self.u64() as i64
  }

  #[inline(always)]
  pub fn bool(&mut self) -> bool {
    self.i64() >= 0
  }

  #[inline(always)]
  pub fn bounded_u32(&mut self, max: u32) -> u32 {
    umulh(self.u64(), (max as u64) + 1) as u32
  }

  #[inline(always)]
  pub fn inclusive_range_u32(&mut self, a: u32, b: u32) -> u32 {
    a.wrapping_add(self.bounded_u32(b.wrapping_sub(a)))
  }
}

pub mod thread_local {
  use super::*;

  std::thread_local! {
    static RNG: core::cell::Cell<u128> = const { core::cell::Cell::new(0) };
  }

  #[inline(always)]
  fn with<F, T>(f: F) -> T
  where
    F: FnOnce(&mut Rng) -> T
  {
    RNG.with(|cell| {
      let mut g =
        match NonZeroU128::new(cell.get()) {
          None => Rng::from_entropy(),
          Some(s) => Rng::new(s)
        };
      let x = f(&mut g);
      cell.set(g.state().get());
      x
    })
  }

  pub fn split() -> Rng {
    with(Rng::split)
  }

  pub fn u64() -> u64 {
    with(Rng::u64)
  }
}
