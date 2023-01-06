use crate::prelude::*;

#[derive(Clone, Copy)]
pub struct Rng {
  x: u64,
  y: u64,
}

#[inline]
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

  #[inline] 
  pub fn next(self) -> (Self, u64) {
    let Self { x, y } = self;

    let u = x.rotate_right(7) ^ y;
    let v = x ^ x >> 19;
    let w = x.wrapping_mul(y) ^ umulh(x, y);
    let z = u.wrapping_add(w);

    (Self { x: u, y: v }, z)
  }
}

pub struct ThreadLocalRng {
  rng: Cell<Rng>,
}

impl ThreadLocalRng {
  pub fn from_system_seed() -> Self {
    let mut seed = [0; 16];
    getrandom::getrandom(&mut seed).unwrap();
    Self { rng: Cell::new(Rng::from_seed(seed)) }
  }

  pub fn u64x2(&self) -> [u64; 2] {
    let s = self.rng.get();
    let (s, a) = s.next();
    let (s, b) = s.next();
    self.rng.set(s);
    [a, b]
  }
}

std::thread_local! {
  pub static THREAD_LOCAL_RNG: ThreadLocalRng =
    ThreadLocalRng::from_system_seed();
}
