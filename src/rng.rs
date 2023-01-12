use crate::prelude::*;

#[derive(Clone)]
pub struct Rng {
  state: NonZeroU128,
}

#[inline(always)]
const fn umulh(x: u64, y: u64) -> u64 {
  (((x as u128) * (y as u128)) >> 64) as u64
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
  pub const fn state(&self) -> NonZeroU128 {
    self.state
  }

  #[inline]
  pub fn u64(&mut self) -> u64 {
    let s = self.state;

    let s = u128::from(s);
    let u = s as u64;
    let v = (s >> 64) as u64;

    let x = u.rotate_right(7) ^ v;
    let y = u ^ u >> 19;
    let z = (u.wrapping_mul(v) ^ umulh(u, v)).wrapping_add(x);

    let s = (x as u128) | ((y as u128) << 64);
    let s = unsafe { NonZeroU128::new_unchecked(s) };

    self.state = s;
    z
  }

  #[inline]
  pub fn array_u64<const N: usize>(&mut self) -> [u64; N] {
    array::from_fn(|_| self.u64())
  }
}

std::thread_local! {
  static THREAD_LOCAL: Cell<u128> = const { Cell::new(0) };
}

// NB: This function doesn't check whether `f` itself calls `with_thread_local`
// and reads a stale state.
//
// So we don't expose this function and instead just use it to implement a few
// other things.

#[inline(always)]
fn internal_with_thread_local<F, A>(f: F) -> A where F: FnOnce(&mut Rng) -> A {
  THREAD_LOCAL.with(|t| {
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
pub fn array_u64<const N: usize>() -> [u64; N] {
  internal_with_thread_local(|g| g.array_u64())
}
