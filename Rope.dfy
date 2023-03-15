include "Utils.dfy"

module BinaryTree {
  import opened Utils
  trait Node
  {
    var height: nat;

    function length(): nat
      reads this
      decreases this.height
  }

  class NTNode extends Node
  {
    var leftLen: nat;
    var left: Node?;
    var right: Node?;

    constructor (left: Node, right: Node)
      ensures this.leftLen == left.length()
      ensures this.height > left.height
      ensures this.height > right.height
    {
      this.left := left;
      this.right := right;
      this.leftLen := left.length();
      this.height := max(left.height, right.height) + 1;
    }

    function length(): nat
      reads this
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
    { |this.str| }
  }
}