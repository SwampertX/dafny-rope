module Rope {
    class Rope {
        ghost var Contents: string;
        ghost var Repr: set<Rope>;

        var data: string;
        var weight: nat;
        var left: Rope?;
        var right: Rope?;

        ghost predicate Valid() 
            reads this, Repr
            ensures Valid() ==> this in Repr
        {
            this in Repr &&
            (left != null ==> 
                left in Repr &&
                left.Repr < Repr && this !in left.Repr &&
                left.Valid() &&
                (forall child :: child in left.Repr ==> child.weight <= weight)) &&
            (right != null ==> 
                right in Repr &&
                right.Repr < Repr && this !in right.Repr &&
                right.Valid()) &&
            (left == null && right == null ==>
                Repr == {this} &&
                Contents == data &&
                weight == |data| &&
                data != "") &&
            (left != null && right == null ==>
                Repr == {this} + left.Repr &&
                Contents == left.Contents &&
                weight == |left.Contents| &&
                data == "") &&
            (left == null && right != null ==>
                Repr == {this} + right.Repr &&
                Contents == right.Contents &&
                weight == 0 &&
                data == "") &&
            (left != null && right != null ==>
                Repr == {this} + left.Repr + right.Repr &&
                left.Repr !! right.Repr &&
                Contents == left.Contents + right.Contents &&
                weight == |left.Contents| &&
                data == "") 
        }

        static lemma contentSizeGtZero(n: Rope)
            requires n.Valid()
            ensures |n.Contents| > 0
            decreases n.Repr
        {}

        function getWeightsOfAllRightChildren(): nat
            reads right, Repr
            requires Valid()
            decreases Repr
            ensures right != null
                ==> getWeightsOfAllRightChildren() == |right.Contents|
        {
            if right == null then 0 else right.weight + right.getWeightsOfAllRightChildren()
        } 

        function length(): nat
            reads Repr
            requires Valid()
            ensures |Contents| == length()
        {
            this.weight + getWeightsOfAllRightChildren()
        }

        // constructor for creating a terminal node
        constructor Terminal(x: string)
            requires x != ""
            ensures Valid() && fresh(Repr) && left == null && right == null && data == x
        { 
            data := x;
            weight := |x|;
            left := null;
            right := null;
            Contents := x;
            Repr := {this};
        }   

        predicate isTerminal(n: Rope)
            reads n, n.left, n.right
        { n.left == null && n.right == null }

        // constructor for creating a non-terminal node
        constructor NonTerminal(nLeft: Rope, nRight: Rope)
            requires nLeft.Valid() && nRight.Valid() && nLeft.Repr !! nRight.Repr
            ensures Valid() && left == nLeft && right == nRight && fresh(Repr - nLeft.Repr - nRight.Repr)
        { 
            left := nLeft;
            right := nRight;
            data := "";

            var nTemp := nLeft;
            var w := 0;
            ghost var nodesTraversed : set<Rope> := {};

            while (nTemp.right != null)
                invariant nTemp != null
                invariant nTemp.Valid()
                invariant forall node :: node in nodesTraversed ==> node.weight <= w
                invariant nodesTraversed == nLeft.Repr - nTemp.Repr
                invariant nTemp.right == null ==> w + nTemp.weight == |nLeft.Contents|
                invariant nTemp.right != null ==> w + nTemp.weight + |nTemp.right.Contents| == |nLeft.Contents| 
                decreases nTemp.Repr
            {
                w := w + nTemp.weight;
                assert w >= 0;
                if (nTemp.left != null) {
                    nodesTraversed := nodesTraversed + nTemp.left.Repr + {nTemp};
                } else {
                    nodesTraversed := nodesTraversed + {nTemp};
                }
                nTemp := nTemp.right;
            }
            w := w + nTemp.weight;
            if (nTemp.left != null) {
                nodesTraversed := nodesTraversed + nTemp.left.Repr + {nTemp};
            } else {
                nodesTraversed := nodesTraversed + {nTemp};
            }
            weight := w;

            Contents := nLeft.Contents + nRight.Contents;
            Repr := {this} + nLeft.Repr + nRight.Repr;
        }   

        method getCharAtIndex(index: nat) returns (c: char)
            requires Valid() && 0 <= index < |Contents|
            ensures c == Contents[index]
        {
            var nTemp := this;
            var i := index;
            while (!isTerminal(nTemp)) 
                invariant nTemp != null;
                invariant nTemp.Valid()
                invariant 0 <= i < |nTemp.Contents|   
                invariant nTemp.Contents[i] == Contents[index] 
                decreases nTemp.Repr
            {
                if (i < nTemp.weight) {
                    nTemp := nTemp.left;
                } else {
                    i := i - nTemp.weight;
                    nTemp := nTemp.right;
                }
            }
            // Have reached the terminal node with index i
            c := nTemp.data[i];
        }

        method report(i: nat, j: nat) returns (s: string)
            requires 0 <= i <= j <= |this.Contents|
            requires Valid()
            ensures s == this.Contents[i..j]
            decreases Repr
        {
            if i == j {
                s := "";
            } else {
                if this.left == null && this.right == null {
                    s := data[i..j];
                    // strange: removing this assert fails the postcondition.
                    assert s == this.Contents[i..j];
                } else {
                    if (j <= this.weight) {
                        var s' := this.left.report(i, j);
                        s := s';
                    } else if (this.weight <= i) {
                        var s' := this.right.report(i - this.weight, j - this.weight);
                        s := s';
                        // strange: removing this assert fails the postcondition.
                        assert s == this.Contents[i..j];
                    } else {
                        assert i <= this.weight < j;
                        assert this.weight == |this.left.Contents|;
                        var s1 := this.left.report(i, this.weight);
                        var s2 := this.right.report(0, j - this.weight);
                        s := s1 + s2;
                    }
                }
            }
        }

        method toString() returns (s: string)
            requires Valid()
            ensures s == Contents
        {
            s := report(0, this.length());
        }

        static method concat(n1: Rope?, n2: Rope?) returns (n: Rope?) 
            requires (n1 != null) ==> n1.Valid()
            requires (n2 != null) ==> n2.Valid()
            requires (n1 != null && n2 != null) ==> (n1.Repr !! n2.Repr)
            ensures (n1 != null || n2 != null) ==> n != null && n.Valid()
            ensures (n1 == null && n2 == null) ==> n == null
            ensures (n1 == null && n2 != null) ==> n == n2 && n != null && n.Valid() && n.Contents == n2.Contents
            ensures (n1 != null && n2 == null) ==> n == n1 && n != null && n.Valid() && n.Contents == n1.Contents
            ensures (n1 != null && n2 != null) ==> (n != null && n.Valid() && n.left == n1 && n.right == n2 && 
                                                    n.Contents == n1.Contents + n2.Contents && fresh(n.Repr - n1.Repr - n2.Repr))
        {
            if (n1 == null) {
                n := n2;
            } else if (n2 == null) {
                n := n1;
            } else {
                n := new Rope.NonTerminal(n1, n2);
            } 
        } 


        /**
            Dafny needs help to guess that in our definition, every rope must
            have non-empty Contents, otherwise it is represented by [null].

            The lemma contentSizeGtZero(n) is thus important to prove the
            postcondition of this method, in the two places where the lemma is
            invoked.
        */
        static method split(n: Rope, index: nat) returns (n1: Rope?, n2: Rope?) 
            requires n.Valid() && 0 <= index <= |n.Contents|
            ensures index == 0 ==> (n1 == null && n2 != null && n2.Valid() && n2.Contents == n.Contents && fresh(n2.Repr - n.Repr))
            ensures index == |n.Contents| ==> (n2 == null && n1 != null && n1.Valid() && n1.Contents == n.Contents && fresh(n1.Repr - n.Repr))
            ensures 0 < index < |n.Contents| ==> (n1 != null && n1.Valid() && n2 != null && n2.Valid() && 
                                                    n1.Contents == n.Contents[..index] && n2.Contents == n.Contents[index..] &&
                                                    n1.Repr !! n2.Repr && fresh(n1.Repr - n.Repr) && fresh(n2.Repr - n.Repr))
            decreases n.Repr
        {
            if (index == 0) {
                n1 := null;
                n2 := n;
                Rope.contentSizeGtZero(n);
                // assert index != |n.Contents|;
            } else if (index < n.weight) {
                if (n.left != null) {
                    var s1, s2 := split(n.left, index);
                    n1 := s1;
                    n2 := concat(s2, n.right);
                } else {
                    // terminal node
                    if (index == 0) {
                        n1 := null;
                        n2 := n;
                    } else {
                        n1 := new Rope.Terminal(n.data[..index]);
                        n2 := new Rope.Terminal(n.data[index..]);
                    }
                }
            } else if (index > n.weight) {
                var s1, s2 := split(n.right, index - n.weight);
                n1 := concat(n.left, s1);
                n2 := s2;
            } else {
                // since [n.weight == index != 0], it means that [n] cannot be a
                // non-terminal node with [left == null].
                if (n.left != null && n.right == null) {
                    n1 := n.left;
                    n2 := null;
                } else if (n.left != null && n.right != null) {
                    n.contentSizeGtZero(n.right);
                    // assert index != |n.Contents|;
                    n1 := n.left;
                    n2 := n.right;
                } else {
                    assert n.left == null && n.right == null;
                    n1 := n;
                    n2 := null;
                }
            }
        }

        static method insert(n1: Rope, n2: Rope, index: nat) returns (n: Rope)
            requires n1.Valid() && n2.Valid() && n1.Repr !! n2.Repr
            requires 0 <= index < |n1.Contents|
            ensures n.Valid() && n.Contents == n1.Contents[..index] + n2.Contents + n1.Contents[index..] && fresh(n.Repr - n1.Repr - n2.Repr)
        {
            var n1BeforeIndex, n1AfterIndex := split(n1, index);
            var firstPart := concat(n1BeforeIndex, n2);
            n := concat(firstPart, n1AfterIndex);
        }

        static method delete(n: Rope, i: nat, j: nat) returns (m: Rope?)
            requires n.Valid()
            requires 0 <= i < j <= |n.Contents|
            ensures (i == 0 && j == |n.Contents|) <==> m == null
            ensures m != null ==>
                m.Valid() &&
                m.Contents == n.Contents[..i] + n.Contents[j..] &&
                fresh(m.Repr - n.Repr)
        {
            var l1, l2 := split(n, i);
            var r1, r2 := split(l2, j - i);
            m := concat(l1, r2);
        }

        static method substring(n: Rope, i: nat, j: nat) returns (m: Rope?)
            requires n.Valid()
            requires 0 <= i < j <= |n.Contents|
            ensures (i == j) <==> m == null
            ensures m != null ==>
                m.Valid() &&
                m.Contents == n.Contents[i..j] &&
                fresh(m.Repr - n.Repr)
        {
            var l1, l2 := split(n, i);
            var r1, r2 := split(l2, j - i);
            m := r1;
        }

    }
    // End of Rope Class
}
// End of Rope Module
