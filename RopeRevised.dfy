include "Utils.dfy"

module Rope {
    import opened Utils
    datatype traversalState = before | reading

    class Node {
        ghost var Contents: string;
        ghost var Repr: set<Node>;

        var data: string;
        var weight: nat;
        var left: Node?;
        var right: Node?;

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

        function getWeightsOfAllRightChildren(): nat
            reads right, Repr
            requires Valid()
            decreases Repr
        {
            if right == null then 0 else right.weight + right.getWeightsOfAllRightChildren()
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

        // constructor for creating a non-terminal node
        constructor NonTerminal(nLeft: Node, nRight: Node)
            requires nLeft.Valid() && nRight.Valid() && nLeft.Repr !! nRight.Repr
            ensures Valid() && left == nLeft && right == nRight && fresh(Repr - nLeft.Repr - nRight.Repr)
        { 
            left := nLeft;
            right := nRight;
            data := "";

            var nTemp := nLeft;
            var w := 0;
            ghost var nodesTraversed : set<Node> := {};

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

            while (!(nTemp.left == null && nTemp.right == null)) 
                invariant nTemp != null
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

        method getCharAtIndexNew(index: nat) returns (nTemp: Node, i: nat, c: char)
            requires Valid() && 0 <= index < |Contents|
            ensures c == Contents[index]
            ensures 0 <= i < |nTemp.data|
            ensures nTemp.Valid() && nTemp.data[i] == c
        {
            nTemp := this;
            i := index;

            while (!(nTemp.left == null && nTemp.right == null)) 
                // invariant nTemp != null
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

    }

    method concat(n1: Node?, n2: Node?) returns (n: Node?) 
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
            n := new Node.NonTerminal(n1, n2);
        } 
    } 


    method split(n: Node, index: nat) returns (n1: Node?, n2: Node?) 
        requires n.Valid() && 0 <= index < |n.Contents|
        ensures index == 0 ==> (n1 == null && n2 != null && n2.Valid() && n2.Contents == n.Contents && fresh(n2.Repr - n.Repr))
        ensures index == |n.Contents| ==> (n2 == null && n1 != null && n1.Valid() && n1.Contents == n.Contents && fresh(n1.Repr - n.Repr))
        ensures 0 < index < |n.Contents| ==> (n1 != null && n1.Valid() && n2 != null && n2.Valid() && 
                                                n1.Contents == n.Contents[..index] && n2.Contents == n.Contents[index..] &&
                                                n1.Repr !! n2.Repr && fresh(n1.Repr - n.Repr) && fresh(n2.Repr - n.Repr))
        // ensures forall i,i1,i2,j,j1,j2 :: 0 <= i <= j < |n.Contents|
        //     ==> (i1, i2) == split(n, i)
        decreases n.Repr
    {
        if (index == 0) {
            n1 := null;
            n2 := n;
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
                    n1 := new Node.Terminal(n.data[..index]);
                    n2 := new Node.Terminal(n.data[index..]);
                }
            }
        } else if (index > n.weight) {
            var s1, s2 := split(n.right, index - n.weight);
            n1 := concat(n.left, s1);
            n2 := s2;
        } else {
            if (n.left != null || n.right != null) {
                n1 := n.left;
                n2 := n.right;
            } else {
                // terminal
                n1 := n;
                n2 := null;
            }
        }
    }

    method insert(n1: Node, n2: Node, index: nat) returns (n: Node)
        requires n1.Valid() && n2.Valid() && n1.Repr !! n2.Repr
        requires 0 <= index < |n1.Contents|
        ensures n.Valid() && n.Contents == n1.Contents[..index] + n2.Contents + n1.Contents[index..] && fresh(n.Repr - n1.Repr - n2.Repr)
    {
        var n1BeforeIndex, n1AfterIndex := split(n1, index);
        var firstPart := concat(n1BeforeIndex, n2);
        n := concat(firstPart, n1AfterIndex);
    }

    method delete(n: Node, start: nat, length: nat) returns (m: Node)
        requires n.Valid()
        requires 0 <= start < |n.Contents| && 1 <= length <= |n.Contents| - start
    {
        assert start + length - 1 >= start;
        var l1, l2 := split(n, start);
        var r1, r2 := split(n, start + length - 1);
        m := concat(l1, r2);
    }

}