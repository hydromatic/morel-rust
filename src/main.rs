fn main() {
  println!("Hi, {}", add(3, 4));
}

fn add(a: i32, b: i32) -> i32 {
  a + b
}

#[cfg(test)]
mod test {
  use super::add;

  #[test]
  fn test_add() {
    assert_eq!(add(3, 4), 7);
    assert_eq!(add(-1, 1), 0);
    assert_eq!(add(0, 0), 0);
    assert_eq!(add(-5, -5), -10);
  }
}
