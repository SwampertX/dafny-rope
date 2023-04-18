include "Utils.dfy"

module Rope {
    import Utils
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

        method getCharAtIndex(index: nat) returns (nTemp: Node, i: nat, c: char)
            requires Valid() && 0 <= index < |Contents|
            ensures c == Contents[index]
            ensures 0 <= i < |nTemp.data|
            ensures nTemp.Valid() && nTemp.data[i] == c
            ensures nTemp in Repr && isTerminal(nTemp)
        {
            nTemp := this;
            i := index;
            while (!(nTemp.left == null && nTemp.right == null)) 
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

        // function foldLeft<Q(==)> (xs: seq<Node>, init: Q, f: (Q, Node) -> Q): Q
        //     reads xs
        //     ensures forall n: Node :: foldLeft(xs, f(init, n), f) == foldLeft([n]+xs, init, f)
        // {
        //     if |xs| == 0 then init else foldLeft(xs[1..], f(init, xs[0]), f)
        // }
        method test()
        {
            assert [1,2,3][..1] == [1];
            assert [1,2,3][1..] == [2,3];
        }

        ghost function collectAllData(xs: seq<Node>): string
            reads xs
            requires forall i:: 0 <= i < |xs| ==> xs[i].Valid() && isTerminal(xs[i])
            // ensures forall i :: 0 <= i < |xs|
            //     ==> collectAllData(xs[..i]) + collectAllData(xs[i..]) == collectAllData(xs)
        {
            if |xs| == 0 then "" else xs[0].Contents + collectAllData(xs[1..])
        }

        method collectAllDataM(xs: seq<Node>) returns (s: string)
            requires forall i:: 0 <= i < |xs| ==> xs[i].Valid() && isTerminal(xs[i])
            ensures s == collectAllData(xs)
            // ensures forall i :: 0 <= i < |xs|
            //     ==> collectAllData(xs[..i]) + collectAllData(xs[i..]) == collectAllData(xs)
        {
            var i := 0;
            assert forall i:: 0 <= i < |xs| ==> xs[i].data == xs[i].Contents;
            s := "";
            assert collectAllData(xs[..0]) == "";
            while (i < |xs|)
                invariant 0 <= i <= |xs|
                invariant s == collectAllData(xs[..i])
            {
                s := s + xs[i].data;
                i := i + 1;
            }
            assert xs == xs[..|xs|];
            assert collectAllData(xs) == s;
        }

        function terminalPreOrder(): seq<Node>
            reads Repr
            requires Valid()
            ensures (set n: Node | n in terminalPreOrder()) <= Repr
            ensures forall n :: n in Repr ==> (isTerminal(n) <==> n in terminalPreOrder())
            // ensures foldLeft(terminalPreOrder(),
            //     "", (acc: string, n: Node) => acc + n.data) == Contents
            ensures collectAllData(terminalPreOrder()) == Contents
        {
            if (this.left == null && this.right == null) then [this]
            else if (this.left != null && this.right == null)
                then this.left.terminalPreOrder()
            else if (this.left == null && this.right != null)
                then this.right.terminalPreOrder()
            else this.left.terminalPreOrder() + this.right.terminalPreOrder()
        }

        predicate isTerminal(n: Node)
            reads n, n.left, n.right
        { n.left == null && n.right == null }

        function length(ns: seq<Node>): nat
            reads ns
            requires forall n :: n in ns ==> isTerminal(n)
        {
            if |ns| == 0 then 0 else |ns[0].data| + length(ns[1..])
        }

        // TODO: report with recursive DFS

    //     method report(i: nat, j: nat, last: Node) returns (s: string)
    //         requires Valid() && 0 <= i <= j < |Contents|
    //         requires last.Valid() && last in Repr
    //         ensures s == Contents[i..j]
    //     {
    //         var start: Node, i': nat, tmp1: char := this.getCharAtIndex(i);
    //         var end: Node, j': nat, tmp2: char := this.getCharAtIndex(i);
    //         var order := this.terminalPreOrder();
    //         // assert start in order && end in order;
    //         var i := 0;
    //         // assert |order| >= 1;
    //         s := "";
    //         var state := before;
    //         assert forall o :: o in order ==> isTerminal(o);
    //         var ii := i => Utils.min(i, length(order));
    //         while (i < |order|)
    //             invariant 0 <= i <= |order|
    //             invariant s == Contents[i..Utils.min(j,length(order[..i]))]
    //         {
    //             var curr := order[i];
    //             if state == before {
    //                 if curr == start {
    //                     state := reading;
    //                     s := curr.data[i'..];
    //                 }
    //             } else {
    //                 assert state == reading;
    //                 if curr == end {
    //                     s := s + curr.data[..j'];
    //                     break;
    //                 } else {
    //                     s := s + data;
    //                 }
    //             }
    //             i := i + 1;
    //         }
    //     }

    method delete(start: nat, length: nat) returns (n: Node)
    {
        var lhs := split(start);
        var rhs := split(start + length);
        n := concat(lhs.left, rhs.right);
    }
  }

    }


    method concat(n1: Node?, n2: Node?) returns (n: Node?) 
        requires (n1 != null) ==> n1.Valid()
        requires (n2 != null) ==> n2.Valid()
        requires (n1 != null && n2 != null) ==> (n1.Repr !! n2.Repr)
        ensures (n1 == null && n2 == null) ==> n == null
        ensures (n1 == null && n2 != null) ==> n == n2 && n != null && n.Valid() && n.Contents == n2.Contents
        ensures (n1 != null && n2 == null) ==> n == n1 && n != null && n.Valid() && n.Contents == n1.Contents
        ensures (n1 != null && n2 != null) ==> (n != null && n.Valid() && n.left == n1 && n.right == n2 && n.Contents == n1.Contents + n2.Contents && fresh(n.Repr - n1.Repr - n2.Repr))
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
        requires n.Valid() && 0 < index < |n.Contents|
        // ensures n1 != null ==> n1.Valid() && n1.Contents == old(n.Contents[..index])
        // ensures n2 != null ==> n2.Valid() && n2.Contents == old(n.Contents[index..])
    {
        var nTemp := n;
        var i := index;
        n1 := null;
        n2 := null;

        while (!(nTemp.left == null && nTemp.right == null)) 
            invariant nTemp != null
            invariant nTemp.Valid()
            invariant 0 <= i < |nTemp.Contents|  
            invariant n1 != null ==> n1.Valid() && nTemp.Repr !! n1.Repr
            invariant n2 != null ==> n2.Valid() && nTemp.Repr !! n2.Repr
            invariant n1 == null ==> nTemp.Contents[..i] == old(n.Contents[..index])
            invariant n1 != null ==> n1.Contents + nTemp.Contents[..i] == old(n.Contents[..index])
            invariant n2 == null ==> nTemp.Contents[i..] == old(n.Contents[index..])
            invariant n2 != null ==> nTemp.Contents[i..] + n2.Contents == old(n.Contents[index..])
            invariant nTemp.Contents[i] == n.Contents[index]  
            decreases nTemp.Repr
        {
            if (i < nTemp.weight) {
                var newn2 := concat(nTemp.right, n2);
                assert n2 != null ==> newn2 != null; 
                n2 := newn2;
                nTemp := nTemp.left;
            } else { 
                var newn1 := concat(n1, nTemp.left);
                // weird behaviour - uncommenting asserts causes issues...and postconditions being uncommented makes the passing invariants fail
                assert n1 != null ==> newn1 != null;
                n1 := newn1;
                i := i - nTemp.weight;
                nTemp := nTemp.right;
            }
        }
        
        // Have reached the terminal node with index i
        // Check if need to split leaf node into two parts in new tree
        if (0 < i < nTemp.weight - 1) {
            var splitLeft := new Node.Terminal(nTemp.data[..i]);
            var splitRight := new Node.Terminal(nTemp.data[i..]);
            n1 := concat(n1, splitLeft);
            n2 := concat(splitRight, n2);
        }

    }
}

module Test {
    import opened Rope
    
    method test() {
        var r1 := new Node.Terminal("abcde");
        assert r1.data == "abcde";
    }
}
