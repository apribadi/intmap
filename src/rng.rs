use crate::prelude::*;

#[derive(Clone)]
pub struct Rng(NonZeroU128);

#[inline(always)]
fn mul(x: u64, y: u64) -> u128 {
  (x as u128) * (y as u128)
}

#[inline(always)]
fn lo(x: u128) -> u64 {
  x as u64
}

#[inline(always)]
fn hi(x: u128) -> u64 {
  (x >> 64) as u64
}

#[inline(always)]
fn concat(x: u64, y: u64) -> u128 {
  (x as u128) ^ ((y as u128) << 64)
}

impl Rng {
  #[inline(always)]
  pub const fn new(state: NonZeroU128) -> Self {
    Self(state)
  }

  pub fn from_seed(seed: [u8; 16]) -> Self {
    let s = u128::from_le_bytes(seed);
    let s = s ^ (s == 0) as u128;
    let s = unsafe { NonZeroU128::new_unchecked(s) };
    Self(s)
  }

  pub fn from_u64(n: u64) -> Self {
    const M: u128 = 0x487e_d511_0b46_11a6_2633_145c_06e0_e689;
    let s = concat(n, 1);
    let s = s.wrapping_mul(M);
    let s = s.swap_bytes();
    let s = s.wrapping_mul(M);
    let s = s.swap_bytes();
    let s = s.wrapping_mul(M);
    let s = unsafe { NonZeroU128::new_unchecked(s) };
    Self(s)
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
    let s = self.0.get();
    let a = lo(s);
    let b = hi(s);
    let c = a.rotate_right(7) ^ b;
    let d = a ^ a >> 19;
    let t = mul(a, b);
    let x = c.wrapping_add(lo(t) ^ hi(t));
    let s = concat(c, d);
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
    hi(mul(self.u64(), (max as u64) + 1)) as u32
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
          None => {
            let mut seed = [0; 16];
            getrandom::getrandom(&mut seed).expect("getrandom::getrandom failed!");
            Rng::from_seed(seed)
          }
          Some(s) => {
            Rng::new(s)
          }
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
