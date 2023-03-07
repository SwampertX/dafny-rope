include "BinaryTree.dfy"

module Rope {
  import opened BinaryTree
  type wbt = WeightedBinaryTree<string,nat>

  class Rope {
    const rope: wbt

    constructor (str: string)
    {
      rope := wbt()
    }
  }
}