use crate::prelude::*;

#[derive(Clone)]
pub struct Rng {
  state: NonZeroU128,
}

#[inline(always)]
const fn umulh(x: u64, y: u64) -> u64 {
  (((x as u128) * (y as u128)) >> 64) as u64
}

#[inline(always)]
const fn le_u64x2_from_u128(x: u128) -> [u64; 2] {
  [ x as u64, (x >> 64) as u64 ]
}

#[inline(always)]
const fn u128_from_le_u64x2(x: [u64; 2]) -> u128 {
  (x[0] as u128) | ((x[1] as u128) << 64)
}

#[inline(never)]
#[cold]
fn get_system_seed() -> NonZeroU128 {
  let mut seed = [0; 16];
  getrandom::getrandom(&mut seed).expect("getrandom::getrandom failed!");
  let seed = u128::from_le_bytes(seed);
  let seed = NonZeroU128::new(seed).expect("getrandom::getrandom returned all zeros!");
  seed
}

impl Rng {
  #[inline]
  pub const fn new(seed: NonZeroU128) -> Self {
    Self { state: seed }
  }

  #[inline]
  pub const fn new_hashed(seed: NonZeroU128) -> Self {
    const M: u128 = 0x9670_4a6b_b5d2_c4fb_3aa6_45df_0540_268d;
    let seed = seed.get();
    let seed = seed.wrapping_mul(M);
    let seed = seed.swap_bytes();
    let seed = seed.wrapping_mul(M);
    let seed = seed.swap_bytes();
    let seed = seed.wrapping_mul(M);
    let seed = unsafe { NonZeroU128::new_unchecked(seed) };
    Self { state: seed }
  }

  #[inline]
  pub const fn state(&self) -> NonZeroU128 {
    self.state
  }

  #[inline]
  pub fn u64(&mut self) -> u64 {
    let s = self.state;

    let [ u, v ] = le_u64x2_from_u128(u128::from(s));

    let x = u.rotate_right(7) ^ v;
    let y = u ^ u >> 19;
    let z = (u.wrapping_mul(v) ^ umulh(u, v)).wrapping_add(x);

    let s = u128_from_le_u64x2([ x, y ]);

    self.state = unsafe { NonZeroU128::new_unchecked(s) };

    z
  }

  #[inline]
  pub fn split(&mut self) -> Self {
    let seed = u128_from_le_u64x2([ self.u64(), self.u64() ]);
    let seed = seed | 1;
    let seed = unsafe { NonZeroU128::new_unchecked(seed) };
    Self::new(seed)
  }

  #[inline]
  pub fn i64(&mut self) -> i64 {
    self.u64() as i64
  }

  #[inline]
  pub fn bool(&mut self) -> bool {
    self.i64() >= 0
  }

  #[inline]
  pub fn bounded_u32(&mut self, max: u32) -> u32 {
    umulh(self.u64(), (max as u64) + 1) as u32
  }

  #[inline]
  pub fn inclusive_range_u32(&mut self, a: u32, b: u32) -> u32 {
    a.wrapping_add(self.bounded_u32(b.wrapping_sub(a)))
  }
}

pub mod thread_local {
  use super::*;

  std::thread_local! {
    static RNG: Cell<u128> = const { Cell::new(0) };
  }

  // NB: This function doesn't check whether `f` itself calls
  // `internal_with_thread_local` and reads another copy of the state.

  #[inline(always)]
  fn internal_with_thread_local<F, A>(f: F) -> A where F: FnOnce(&mut Rng) -> A {
    RNG.with(|t| {
      let s = t.get();
      let s = NonZeroU128::new(s).unwrap_or_else(|| get_system_seed());
      let mut g = Rng::new(s);
      let a = f(&mut g);
      let s = u128::from(g.state());
      t.set(s);
      a
    })
  }

  #[inline]
  pub fn u64() -> u64 {
    internal_with_thread_local(|g| g.u64())
  }

  #[inline]
  pub fn split() -> Rng {
    internal_with_thread_local(|g| g.split())
  }
}
