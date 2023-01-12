use crate::prelude::*;

#[test]
fn test_keys() -> Result<(), std::fmt::Error> {
  let mut s = String::new();

  let mut t = HashMapNZ64::<u64>::new();

  let keys = [
    10,
    5,
    100,
    13,
    1000,
    17,
    10000
  ].map(|x| NonZeroU64::new(x).unwrap());

  for &key in keys.iter() {
    t.insert(key, u64::from(key) - 1);
  }

  writeln!(s, "{:?}", t.items_sorted_by_key())?;

  expect![[r#"
      [(5, 4), (10, 9), (13, 12), (17, 16), (100, 99), (1000, 999), (10000, 9999)]
  "#]].assert_eq(&s);

  Ok(())
}

#[test]
fn test_basic() -> Result<(), std::fmt::Error> {
  let mut s = String::new();
  let mut t = HashMapNZ64::<u64>::new();

  let key = NonZeroU64::new(13).unwrap();

  writeln!(s, "{:?} <- t.len()", t.len())?;
  writeln!(s, "{:?} <- t.is_empty()", t.is_empty())?;
  writeln!(s, "{:?} <- t.contains_key({:?})", t.contains_key(key), key)?;
  writeln!(s, "{:?} <- t.get({:?})", t.get(key), key)?;
  writeln!(s, "{:?} <- t.get_mut({:?})", t.get_mut(key), key)?;
  writeln!(s, "{:?} <- t.insert({:?}, {:?})", t.insert(key, 42), key, 42)?;
  writeln!(s, "{:?} <- t.len()", t.len())?;
  writeln!(s, "{:?} <- t.is_empty()", t.is_empty())?;
  writeln!(s, "{:?} <- t.contains_key({:?})", t.contains_key(key), key)?;
  writeln!(s, "{:?} <- t.get({:?})", t.get(key), key)?;
  writeln!(s, "{:?} <- t.get_mut({:?})", t.get_mut(key), key)?;
  writeln!(s, "{:?} <- t.remove({:?})", t.remove(key), key)?;
  writeln!(s, "{:?} <- t.len()", t.len())?;
  writeln!(s, "{:?} <- t.is_empty()", t.is_empty())?;
  writeln!(s, "{:?} <- t.contains_key({:?})", t.contains_key(key), key)?;
  writeln!(s, "{:?} <- t.get({:?})", t.get(key), key)?;
  writeln!(s, "{:?} <- t.get_mut({:?})", t.get_mut(key), key)?;

  expect![[r#"
      0 <- t.len()
      true <- t.is_empty()
      false <- t.contains_key(13)
      None <- t.get(13)
      None <- t.get_mut(13)
      None <- t.insert(13, 42)
      1 <- t.len()
      false <- t.is_empty()
      true <- t.contains_key(13)
      Some(42) <- t.get(13)
      Some(42) <- t.get_mut(13)
      Some(42) <- t.remove(13)
      0 <- t.len()
      true <- t.is_empty()
      false <- t.contains_key(13)
      None <- t.get(13)
      None <- t.get_mut(13)
  "#]].assert_eq(&s);

  Ok(())
}
