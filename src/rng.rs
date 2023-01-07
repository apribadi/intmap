use crate::prelude::*;

#[derive(Clone)]
pub struct Rng(NonZeroU128);

#[inline(always)]
const fn umulh(x: u64, y: u64) -> u64 {
  (((x as u128) * (y as u128)) >> 64) as u64
}

impl Rng {
  #[inline(always)] 
  pub const fn new(seed: NonZeroU128) -> Self {
    Self(seed)
  }

  #[inline(never)]
  #[cold]
  pub fn from_system_seed() -> Self {
    let mut seed = [0; 16];
    getrandom::getrandom(&mut seed).expect("getrandom::getrandom failed!");
    let seed = u128::from_le_bytes(seed);
    let seed = NonZeroU128::new(seed).expect("getrandom::getrandom returned all zeros!");
    Self::new(seed)
  }

  #[inline(always)] 
  pub fn u64(&mut self) -> u64 {
    let s = self.0;

    let s = u128::from(s);
    let u = s as u64;
    let v = (s >> 64) as u64;

    let x = u.rotate_right(7) ^ v;
    let y = u ^ u >> 19;
    let z = u.wrapping_mul(v) ^ umulh(u, v);
    let z = z.wrapping_add(x);

    let s = (x as u128) | ((y as u128) << 64);
    let s = unsafe { NonZeroU128::new_unchecked(s) };

    self.0 = s;

    z
  }

  #[inline(always)]
  pub fn with_thread_local<F, A>(f: F) -> A where F: FnOnce(&mut Self) -> A {
    THREAD_LOCAL.with(|t| {
      let s = t.get();
      let mut g =
        match NonZeroU128::new(s) {
          None => Rng::from_system_seed(),
          Some(s) => Rng::new(s)
        };
      let a = f(&mut g);
      let s = u128::from(g.0);
      t.set(s);
      a
    })
  }
}

std::thread_local! {
  static THREAD_LOCAL: Cell<u128> = const { Cell::new(0) };
}
