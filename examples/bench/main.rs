mod prelude;
mod maps;

use crate::prelude::*;

const NUM_OPERATIONS: usize = 1_000;
const KEY_ROTATE_LEFT: u32 = 16;

fn sizes() -> Box<[usize]> {
  if false {
    Box::new([
      20_000_usize,
      20_000_usize,
      20_000_usize,
      20_000_usize,
    ])
  } else {
  [
    //1,
    10,
    100,
    1000,
    10000,
    100000,
    // 1000000,
    // 10000000,
  ].iter().flat_map(|a|
    [
      10,
      13,
      18,
      25,
      30,
      40,
      55,
      75,
    ].map(|b| a * b)
  ).collect::<Vec<_>>().into_boxed_slice()
  }
}

#[inline]
fn key_seq(i: usize) -> NonZeroU64 {
  NonZeroU64::new(((i as u64).rotate_left(KEY_ROTATE_LEFT)) | 1).unwrap()
}

fn timeit<F, A>(f: F) -> f64 where F: FnOnce() -> A {
  let start = Instant::now();
  let _: A = core::hint::black_box(f());
  let stop = Instant::now();
  stop.saturating_duration_since(start).as_nanos() as f64
}

fn bench_get_100pct<T: BenchMap>(size: usize) -> f64 {
  let mut g = Rng::from_u64(42);
  let mut t = T::new();
  let mut s = Vec::with_capacity(NUM_OPERATIONS);

  for _ in 0 .. NUM_OPERATIONS {
    let r = g.bounded_u32((size - 1) as u32);
    let k = key_seq(r as usize);
    s.push(k)
  }

  for i in 0 .. size {
    let k = key_seq(i);
    let _ = t.insert(k, u64::from(k));
  }


  /*
  {
    // flush cache
    let mut a = Vec::new();
    for i in 0 .. 128_000_000u64 {
      a.push(i)
    }
    let _:_ = core::hint::black_box(a);
  }
  */

  #[inline(never)]
  fn go<T: BenchMap>(t: &mut T, s: &Vec<NonZeroU64>) -> u64 {
    let mut a: u64 = 0;
    for &k in s.iter() {
      if let Some(v) = t.get(k) {
        a = a.wrapping_add(v);
      }
    }
    a
  }

  let elapsed = timeit(|| go(&mut t, &s));

  elapsed / (NUM_OPERATIONS as f64)
}

fn bench_get_50pct<T: BenchMap>(size: usize) -> f64 {
  let mut g = Rng::from_u64(42);
  let mut t = T::new();
  let mut s = Vec::with_capacity(NUM_OPERATIONS);

  for i in 0 .. size {
    let k = key_seq(i);
    let _ = t.insert(k, u64::from(k));
  }

  for _ in 0 .. NUM_OPERATIONS {
    let r = g.bounded_u32((size - 1) as u32);
    if g.bool() {
      s.push(key_seq(r as usize))
    } else {
      s.push(key_seq((r as usize) + size))
    }
  }

  #[inline(never)]
  fn go<T: BenchMap>(t: &mut T, s: &Vec<NonZeroU64>) -> u64 {
    let mut a: u64 = 0;
    for &k in s {
      if let Some(v) = t.get(k) {
        a = a.wrapping_add(v)
      }
    }
    a
  }

  let elapsed = timeit(|| go(&mut t, &s));

  elapsed / (NUM_OPERATIONS as f64)
}

fn bench_memory<T: BenchMap>(size: usize) -> f64 {
  let mut t = T::new();

  for k in (0 .. size).map(key_seq) {
    let _ = t.insert(k, u64::from(k));
  }

  (t.heap_memory_in_bytes() as f64) / (size as f64)
}

fn bench_remove_insert<T: BenchMap>(size: usize) -> f64 {
  let mut g = Rng::from_u64(42);
  let mut t = T::new();
  let mut a = Vec::from_iter((0 .. size).map(|i| key_seq(i)));
  let mut s = Vec::with_capacity(NUM_OPERATIONS);

  for &k in a.iter() {
    let _ = t.insert(k, u64::from(k));
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

  #[inline(never)]
  fn go<T: BenchMap>(t: &mut T, s: &Vec<NonZeroU64>) -> u64 {
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
  }

  let elapsed = timeit(|| go(&mut t, &s));

  elapsed / (NUM_OPERATIONS as f64)
}

fn warmup() {
  let mut s = 1u64;
  for i in 0 .. 2_000_000_000 { s = s.wrapping_mul(i); }
  let _: u64 = core::hint::black_box(s);
}

fn main() {
  #[inline(never)]
  fn doit<T: BenchMap>(name: &'static str) {
    for &size in sizes().iter() {
      let _ = bench_get_50pct::<T>;
      let _ = bench_get_100pct::<T>;
      let _ = bench_remove_insert::<T>;
      let _ = bench_memory::<T>;
      let nanos = bench_get_100pct::<T>(size);
      println!("{:11} {:9} -> {:4.1} ns/op", name, size, nanos);
      /*
      let nanos = bench_get_50pct::<T>(size);
      println!("{:11} {:9} -> {:4.1} ns/op", name, size, nanos);
      let nanos = bench_remove_insert::<T>(size);
      println!("{:11} {:9} -> {:4.1} ns/op", name, size, nanos);
      */
    }
  }

  warmup();

  // doit::<AHashMap<NonZeroU64, u64>>("AHashMap");
  // doit::<HashMapNZ64<u64>>("HashMapNZ64");
  //
  for &size in sizes().iter() {
    let x = bench_remove_insert::<AHashMap<NonZeroU64, u64>>(size);
    let y = bench_remove_insert::<HashMapNZ64<u64>>(size);
    println!("remove insert {:9} -> {:4.1} - {:4.1} = {:+4.1} ns/op", size, x, y, x - y);
  }

  for &size in sizes().iter() {
    let x = bench_get_100pct::<AHashMap<NonZeroU64, u64>>(size);
    let y = bench_get_100pct::<HashMapNZ64<u64>>(size);
    println!("get 100% {:9} -> {:4.1} - {:4.1} = {:+4.1} ns/op", size, x, y, x - y);
  }

  for &size in sizes().iter() {
    let x = bench_get_50pct::<AHashMap<NonZeroU64, u64>>(size);
    let y = bench_get_50pct::<HashMapNZ64<u64>>(size);
    println!("get 50% {:9} -> {:4.1} - {:4.1} = {:+4.1} ns/op", size, x, y, x - y);
  }

  // doit::<HashMap<NonZeroU64, u64>>("HashMap");
  // doit::<FxHashMap<NonZeroU64, u64>>("FxHashMap");
  // doit::<IntMap<u64>>("IntMap");
  // doit::<BTreeMap<NonZeroU64, u64>>("BTreeMap");
  // doit::<FakeMap>("FakeMap");
  let _ = FakeMap::new();
}
