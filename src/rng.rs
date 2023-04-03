use crate::prelude::*;

#[derive(Clone)]
pub struct Rng(NonZeroU128);

#[inline(always)]
const fn umulh(x: u64, y: u64) -> u64 {
  (((x as u128) * (y as u128)) >> 64) as u64
}

const fn state_from_seed(s: u128) -> NonZeroU128 {
  const M: u128 = 0x9670_4a6b_b5d2_c4fb_3aa6_45df_0540_268d;
  let s = s.wrapping_mul(M);
  let s = s | 1;
  let s = s.swap_bytes();
  let s = s.wrapping_mul(M);
  let s = s.swap_bytes();
  let s = s.wrapping_mul(M);
  unsafe { NonZeroU128::new_unchecked(s) }
}

#[inline(never)]
#[cold]
fn init_state() -> NonZeroU128 {
  let mut seed = [0; 16];
  getrandom::getrandom(&mut seed).expect("getrandom::getrandom failed!");
  state_from_seed(u128::from_le_bytes(seed))
}

impl Rng {
  pub const fn from_state(state: NonZeroU128) -> Self {
    Self(state)
  }

  pub const fn from_seed(seed: u128) -> Self {
    Self::from_state(state_from_seed(seed))
  }

  pub const fn state(&self) -> NonZeroU128 {
    self.0
  }

  #[inline(always)]
  pub fn u64(&mut self) -> u64 {
    const M: u64 = 0x9e37_79b9_7f4a_7c15;

    let s = self.0.get();
    let a = s as u64;
    let b = (s >> 64) as u64;

    let c = a.rotate_right(7) ^ b;
    let d = a ^ a >> 19;
    let x = a ^ b.wrapping_mul(M).wrapping_add(umulh(b, M));

    let s = (c as u128) | ((d as u128) << 64);
    self.0 = unsafe { NonZeroU128::new_unchecked(s) };

    x
  }

  #[inline(always)]
  pub fn split(&mut self) -> Self {
    let a = self.u64();
    let b = self.u64();
    let s = (a as u128) | ((b as u128) << 64);
    let s = s | 1;
    let s = unsafe { NonZeroU128::new_unchecked(s) };
    Self::from_state(s)
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
    static RNG: Cell<u128> = const { Cell::new(0) };
  }

  #[inline(always)]
  fn with<F, A>(f: F) -> A
  where
    F: FnOnce(&mut Rng) -> A
  {
    RNG.with(|cell| {
      let s = NonZeroU128::new(cell.get()).unwrap_or_else(init_state);
      let mut g = Rng::from_state(s);
      let x = f(&mut g);
      let s = g.state().get();
      cell.set(s);
      x
    })
  }

  #[inline(always)]
  pub fn u64() -> u64 {
    with(|g| g.u64())
  }

  #[inline(always)]
  pub fn split() -> Rng {
    with(|g| g.split())
  }
}
