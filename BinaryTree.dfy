include "Utils.dfy"

module WeightedBinaryTree {
  import opened Utils
  datatype WeightedBinaryTree<T, S> =
    | Node(data: T)
    | Parent(value: S, left: WeightedBinaryTree<T, S>, right: WeightedBinaryTree<T, S>)


  predicate isNull<T, S>(n: WeightedBinaryTree<T, S>) {
    match n {
      case Node(_) => true
      case _ => false
    }
  }

  function method size<T, S>(n: WeightedBinaryTree<T, S>): nat
    ensures size(n) >= 1
  {
    match n {
      case Node => 1
      case Parent(val, left, right) => 1 + size(left) + size(right)
    }
  }

  function method height<T, S>(n: WeightedBinaryTree<T, S>): nat
    ensures height(n) >= 0
  {
    match n {
      case Node => 0
      case Parent(val, left, right) => 1 + max(height(left), height(right))
    }
  }

  function method mapt<T,S,U,V>(n: WeightedBinaryTree<T, S>, fnode: T->U, fparent: S->V)
    // returns (m: WeightedBinaryTree<U, V>)
    : WeightedBinaryTree<U,V>
    ensures size(n) == size(mapt(n, fnode, fparent))
    ensures height(n) == height(mapt(n, fnode, fparent))
    ensures isNull(n) <==> isNull(mapt(n,fnode, fparent))
  {
    match n {
      case Node(data) => Node(fnode(data))
      case Parent(val, left, right) =>
        Parent(fparent(val), mapt(left, fnode, fparent), mapt(right, fnode, fparent))
    }
  }

  function method fold<T, S, R>(n: WeightedBinaryTree<T, S>, fnode: T -> R, fparent: (S, R, R) -> R)
    // returns (r: R)
    : R
  {
    match n {
      case Node(data) => fnode(data)
      case Parent(val, left, right) =>
        fparent(val,
            fold(left, fnode, fparent),
            fold(right, fnode, fparent))
    }
  }

  method inOrder<T,S,U>(n: WeightedBinaryTree<T, S>, fnode: T->U, fparent: (U, S, U) -> U)
    returns (u: U)
  {
    u := fold(n, fnode, (val, left, right) => fparent(left, val, right));
  }
}
