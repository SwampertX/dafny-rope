module Utils {
  function max(a: int, b: int): int
    ensures max(a, b) >= a
    ensures max(a, b) >= b
    ensures max(a, b) == a || max(a, b) == b
  {
    if a >= b then a else b
  }

  function min(a: int, b: int): int
    ensures min(a, b) <= a
    ensures min(a, b) <= b
    ensures min(a, b) == a || min(a, b) == b
  {
    if a <= b then a else b
  }
}