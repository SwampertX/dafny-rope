include "BinaryTree.dfy"

module Rope {
  import opened WeightedBinaryTree

  type Rope = WeightedBinaryTree<string, nat>

  method stringToRope(s: string) returns (r: Rope)
  {
    return Node(s);
  }

  method RopeToString(r: Rope) returns (s: string)
  {
    return inOrder(r, x => x, (l, w, r) => l + r);
  }

}