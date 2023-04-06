include "Utils.dfy"

module BinaryTree {
  import opened Utils
  trait Node
  {
    var left: Node?;
    var right: Node?;
    var height: nat;

    function length(): nat
      reads this, this.right
      decreases height
  }

  class NTNode extends Node
  {
    ghost var Repr: set<object>

    predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
    {
      this in Repr &&
      (this.left != null ==> this.left in Repr)
    }
    var leftLen: nat;

    predicate valid()
      reads this, this.left, this.right
    {
      (this.left != null ==> this.leftLen == this.left.length()) &&
      (this.left != null ==> this.height > this.left.height) &&
      (this.right != null ==> this.height > this.right.height)
    }

    constructor (left: Node, right: Node)
      ensures this.leftLen == left.length()
      ensures this.height > left.height
      ensures this.height > right.height
      ensures this.height == max(left.height, right.height) + 1
    {
      this.left := left;
      this.right := right;
      this.leftLen := left.length();
      this.height := max(left.height, right.height) + 1;
    }

    function length(): nat
      reads this, this.right
      decreases height
    {
      this.leftLen + (if this.right == null then 0 else this.right.length())
    }
  }

  class TNode extends Node
  {
    var str: string;

    constructor(str: string)
    {
      this.str := str;
      this.height := 1;
    }

    function length(): nat
      reads this
      decreases height
    { |this.str| }
  }
}