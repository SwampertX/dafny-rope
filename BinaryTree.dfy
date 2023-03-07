module BinaryTree {
  class Rope {
    var children: array<Rope>
    var leftLen: nat
    var data: string

    constructor (left: Rope, right: Rope)
    {
      this.children := new Rope[][left, right];
      this.leftLen := left.length();
      this.data := "";
    }

    constructor fromStr(str: string)
    {
      leftLen := |str|;
      data := str;
    }



    method length() returns (l: nat)
    {
      var r := this.children[1];
      l := this.leftLen;
      while (r != null)
        
      {
        l := l + right.leftLen;
        r := r.right;
      }
      return l;
    }
  }
}