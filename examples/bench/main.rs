mod prelude;
mod maps;

use crate::prelude::*;

const NUM_OPERATIONS: usize = 100_000;
const KEY_ROTATE_LEFT: u32 = 1;
// const KEY_ROTATE_LEFT: u32 = 16;

const SIZES: &[usize] = &[
  10,
  20,
  50,
  100,
  200,
  500,
  1_000,
  2_000,
  5_000,
  10_000,
  20_000,
  50_000,
  100_000,
  200_000,
  500_000,
  1_000_000,
];

#[inline]
fn key_seq(i: usize) -> NonZeroU64 {
  NonZeroU64::new(((i as u64).rotate_left(KEY_ROTATE_LEFT)) | 1).unwrap()
}

fn timeit<F, A>(f: F) -> f64 where F: FnOnce() -> A {
  let start = Instant::now();
  let x: A = f();
  let stop = Instant::now();
  let _: A = hint::black_box(x);
  stop.saturating_duration_since(start).as_nanos() as f64
}

fn bench_get_100pct<T: BenchMap>(size: usize) -> f64 {
  let mut g = Rng::new_hashed(NonZeroU128::new(42).unwrap());
  let mut t = T::new();
  let mut s = Vec::with_capacity(NUM_OPERATIONS);

  for i in 0 .. size {
    let k = key_seq(i);
    t.insert(k, u64::from(k));
  }

  for _ in 0 .. NUM_OPERATIONS {
    let r = g.bounded_u32((size - 1) as u32);
    let k = key_seq(r as usize);
    s.push(k)
  }

  let elapsed = timeit(|| {
    let mut a: u64 = 0;
    for k in s {
      if let Some(v) = t.get(k) {
        a = a.wrapping_add(v)
      }
    }
    a
  });

  elapsed / (NUM_OPERATIONS as f64)
}

fn bench_get_50pct<T: BenchMap>(size: usize) -> f64 {
  let mut g = Rng::new_hashed(NonZeroU128::new(42).unwrap());
  let mut t = T::new();
  let mut s = Vec::with_capacity(NUM_OPERATIONS);

  for i in 0 .. size {
    let k = key_seq(i);
    t.insert(k, u64::from(k));
  }

  for _ in 0 .. NUM_OPERATIONS {
    let r = g.bounded_u32((size - 1) as u32);
    if g.bool() {
      s.push(key_seq(r as usize))
    } else {
      s.push(key_seq((r as usize) + size))
    }
  }

  let elapsed = timeit(|| {
    let mut a: u64 = 0;
    for k in s {
      if let Some(v) = t.get(k) {
        a = a.wrapping_add(v)
      }
    }
    a
  });

  elapsed / (NUM_OPERATIONS as f64)
}

fn bench_memory<T: BenchMap>(size: usize) -> f64 {
  let mut t = T::new();

  for k in (0 .. size).map(key_seq) {
    t.insert(k, u64::from(k));
  }

  (t.heap_memory_in_bytes() as f64) / (size as f64)
}

fn bench_remove_insert<T: BenchMap>(size: usize) -> f64 {
  let mut g = Rng::new_hashed(NonZeroU128::new(42).unwrap());
  let mut t = T::new();
  let mut a = Vec::from_iter((0 .. size).map(|i| key_seq(i)));
  let mut s = Vec::with_capacity(NUM_OPERATIONS);

  for &k in a.iter() {
    t.insert(k, u64::from(k));
  }

  let mut i: usize = 0;

  loop {
    if i == NUM_OPERATIONS { break; }
    let r = g.bounded_u32((size - 1) as u32) as usize;
    let k = a[r];
    s.push(k);
    i = i + 1;
    if i == NUM_OPERATIONS { break; }
    let k = key_seq(i + size);
    a[r] = k;
    s.push(k);
    i = i + 1;
  }

  let elapsed = timeit(|| {
    let mut a: u64 = 0;
    let mut i: usize = 0;
    loop {
      if i == NUM_OPERATIONS { break; }
      let k = s[i];
      if let Some(v) = t.remove(k) { a = a.wrapping_add(v) }
      i = i + 1;
      if i == NUM_OPERATIONS { break; }
      let k = s[i];
      if let Some(v) = t.insert(k, u64::from(k)) { a = a.wrapping_add(v) }
      i = i + 1;
    }
    a
  });

  elapsed / (NUM_OPERATIONS as f64)
}

fn main() {
  fn go<T: BenchMap>(name: &'static str) {
    for &size in SIZES {
      let _ = bench_get_50pct::<T>;
      let _ = bench_get_100pct::<T>;
      let _ = bench_remove_insert::<T>;
      let _ = bench_memory::<T>;
      let nanos = bench_get_100pct::<T>(size);
      println!("{:11} {:9} -> {:4.0} ns/op", name, size, nanos);
    }
  }
  go::<HashMap<NonZeroU64, u64>>("HashMap");
  go::<AHashMap<NonZeroU64, u64>>("AHashMap");
  go::<HashMapNZ64<u64>>("HashMapNZ64");
  go::<FxHashMap<NonZeroU64, u64>>("FxHashMap");
  go::<IntMap<u64>>("IntMap");
  // go::<FakeMap>("FakeMap");
  //
  /*
  fn go2<T: BenchMap>(name: &'static str) {
    for &size in SIZES {
      let x = bench_memory::<T>(size);
      println!("{:11} {:9} -> {:4.1} bytes/item", name, size, x);
    }
  }
  go2::<AHashMap<NonZeroU64, u64>>("AHashMap");
  go2::<HashMapNZ64<u64>>("HashMapNZ64");
  */
}
