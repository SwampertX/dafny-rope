include "Utils.dfy"

module Rope {
    import opened Utils

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
            ensures Valid() && fresh(Repr)
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
                // invariant nTemp.left != null ==> nTemp.weight == |nTemp.left.Contents|
                invariant forall node :: node in nodesTraversed ==> node.weight <= w
                // invariant forall node :: node in nodesTraversed ==> node in nLeft.Repr
                invariant nodesTraversed == nLeft.Repr - nTemp.Repr
                // invariant nTemp.right == null ==> nodesTraversed 
                invariant nTemp.right == null ==> w + nTemp.weight == |nLeft.Contents|
                invariant nTemp.right != null ==> w + nTemp.weight + |nTemp.right.Contents| == |nLeft.Contents| 
                // invariant nTemp.right != null ==> nLeft.Repr == Repr + nTemp.right.Repr
                // invariant forall child :: child in nLeft.Repr ==> child.weight
                // invariant w <= nTemp.Contents
                decreases nTemp.Repr
            {
                // nTemp.right.right != null ==> w + nTemp.weight + nTemp.right.weight + |nTemp.right.right.Contents| == |nTemp.right.Contents|
                w := w + nTemp.weight;
                assert w >= 0;
                if (nTemp.left != null) {
                    nodesTraversed := nodesTraversed + nTemp.left.Repr + {nTemp};
                } else {
                    nodesTraversed := nodesTraversed + {nTemp};
                }
                // nTemp.right.right != null ==> w + nTemp.right.weight + |nTemp.right.right.Contents| == |nTemp.right.Contents|
                // assert nodesTraversed == nLeft.Repr - nTemp.right.Repr;
                nTemp := nTemp.right;
                // assert nodesTraversed == nLeft.Repr - nTemp.Repr;
                // nTemp.right != null ==> w + nTemp.weight + |nTemp.right.Contents| == |nTemp.Contents|
            }
            w := w + nTemp.weight;
            if (nTemp.left != null) {
                nodesTraversed := nodesTraversed + nTemp.left.Repr + {nTemp};
            } else {
                nodesTraversed := nodesTraversed + {nTemp};
            }
            weight := w;
            // assert nLeft.weight <= |nLeft.Contents|;
            // assert |nLeft.Contents| == w;
            // assert nLeft.left != null ==> forall child :: child in nLeft.left.Repr ==> child.weight <= nLeft.weight;
            // assert nLeft.weight <= w;
            // assert nLeft.right != null ==> nLeft.right.weight <= w;

            Contents := nLeft.Contents + nRight.Contents;
            Repr := {this} + nLeft.Repr + nRight.Repr;
        }   

    }

    method concat(n1: Node, n2: Node) returns (n: Node) 
        requires n1.Valid() && n2.Valid() && n1.Repr !! n2.Repr
        ensures n.Valid() && n.Contents == n1.Contents + n2.Contents
    {
        n := new Node.NonTerminal(n1, n2);
    } 
}

