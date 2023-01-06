use crate::prelude::*;

#[derive(Clone)]
pub struct Rng {
  x: u64,
  y: u64,
}

#[inline(always)]
const fn umulh(x: u64, y: u64) -> u64 {
  (((x as u128) * (y as u128)) >> 64) as u64
}

impl Rng {
  pub fn from_seed(seed: [u8; 16]) -> Self {
    let seed = u128::from_le_bytes(seed);
    let seed = if seed == 0 { 0xbaad_5eed_baad_5eed } else { seed };
    let x = seed as u64;
    let y = (seed >> 64) as u64;
    Self { x, y }
  }

  pub fn from_system_seed() -> Self {
    let mut seed = [0; 16];
    getrandom::getrandom(&mut seed).expect("getrandom::getrandom failed!");
    Self::from_seed(seed)
  }

  #[inline(always)] 
  pub fn u64(&mut self) -> u64 {
    let x = self.x;
    let y = self.y;

    let u = x.rotate_right(7) ^ y;
    let v = x ^ x >> 19;
    let w = x.wrapping_mul(y) ^ umulh(x, y);
    let z = u.wrapping_add(w);

    self.x = u;
    self.y = v;

    z
  }

  #[inline(always)]
  pub fn with_thread_local<F, A>(f: F) -> A where F: FnOnce(&mut Self) -> A {
    THREAD_LOCAL.with(|t| {
      // SAFETY:
      //
      // There is no fundamental reason why `Rng` doesn't implement `Copy`; it is
      // only omitted to make the API harder to misuse.
      //
      // So we do essentially the same thing as `Cell::get` and make a copy as
      // we read the value.

      let p = t.as_ptr();
      let mut g = unsafe { p.read() };
      let a = f(&mut g);
      t.set(g);
      a
    })
  }
}

std::thread_local! {
  pub static THREAD_LOCAL: Cell<Rng> =
    Cell::new(Rng::from_system_seed());
}
