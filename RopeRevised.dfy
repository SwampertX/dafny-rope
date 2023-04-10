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

        method getCharAtIndex(index: nat) returns (c: char)
            requires Valid() && 0 <= index < |Contents|
            ensures c == Contents[index]
        {
            var nTemp := this;
            var i := index;

            // assert (nTemp.weight > 0) ==> (nTemp.weight != 0);
            // assert (left == null && right != null) ==> weight == 0;
            // assert (nTemp.left == null && nTemp.right != null) ==> nTemp.weight == 0;
            // assert (nTemp.weight > 0) ==> (nTemp.left == null && nTemp.right == null) || (nTemp.left != null || nTemp.right == null);
            // assert (nTemp.weight > 0 && (nTemp.left != null || nTemp.right != null)) ==> nTemp.left != null;

            // assert (nTemp.weight < |nTemp.Contents|) ==> nTemp.right != null;
            // assert (|nTemp.Contents| > i >= nTemp.weight >= 0) ==>

            while (!(nTemp.left == null && nTemp.right == null)) 
                invariant nTemp != null
                invariant nTemp.Valid()
                invariant 0 <= i < |nTemp.Contents|   
                invariant nTemp.Contents[i] == Contents[index] 
                decreases nTemp.Repr
            {
                if (i < nTemp.weight) {
                    // assert nTemp.weight > 0;
                    // assert !(nTemp.left == null && nTemp.right == null);
                    // assert (nTemp.weight > 0 && (nTemp.left != null || nTemp.right != null)) ==> nTemp.left != null;
                    // assert nTemp.left != null;
                    nTemp := nTemp.left;
                    // assert nTemp != null;
                } else {
                    i := i - nTemp.weight;
                    // assert nTemp.right != null;
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
        ensures (n1 == null && n2 == null) ==> n == null
        ensures (n1 == null && n2 != null) ==> n == n2
        ensures (n1 != null && n2 == null) ==> n == n1
        ensures (n1 != null && n2 != null) ==> (n != null && n.Valid() && n.Contents == n1.Contents + n2.Contents)
    {
        if (n1 == null) {
            n := n2;
        } else if (n2 == null) {
            n := n1;
        } else {
            n := new Node.NonTerminal(n1, n2);
        } 
    } 

    // method split(n: Node, index: nat) returns (n1: Node?, n2: Node?) 
    //     requires n.Valid() && 0 <= index < |n.Contents|
    //     // ensures index == 0 ==> n1 == null && n2 != null && n2.Contents == n.Contents
    //     // ensures index == |n.Contents| - 1 ==> n2 == null && n1 != null && n1.Contents == n.Contents
    //     // ensures 0 < index < |n.Contents| - 1 ==> n1 != null && n2 != null && 
    //     //                                          n1.Valid() && n2.Valid() && 
    //     //                                          n.Contents == n1.Contents + n2.Contents &&
    //     //                                          n1.Contents == n.Contents[..index] && n2.Contents == n.Contents[index..]
    //     // ensures n1 != null && n2 != null ==> n1.Repr !! n2.Repr
    // {
    //     var nTemp := n;
    //     var i := index;
    //     n1 := null;
    //     n2 := null;

    //     if (index == 0) {
    //         n1 := null;
    //         n2 := n;
    //         return;
    //     }
    //     // ghost var leftSize := 0;
    //     // ghost var rightSize := |n.Contents| - 1;
    //     // // ghost var otherSide := 0;
    //     // // assert nTemp.weight <= |n.Contents|;

    //     while (!(nTemp.left == null && nTemp.right == null)) 
    //         invariant i >= 0
    //         invariant nTemp != null
    //         decreases nTemp.Repr
    //     {
    //         if (i < nTemp.weight) {
    //             assert nTemp.weight > 0;
    //             assert !(nTemp.left == null && nTemp.right == null);
    //             assert (nTemp.weight > 0 && (nTemp.left != null || nTemp.right != null)) ==> nTemp.left != null;
    //             nTemp := nTemp.left;
    //         } else {
    //             i := i - nTemp.weight;
    //             nTemp := nTemp.right;
    //         }
    //     }

    //     // while (!(nTemp.left == null && nTemp.right == null))
    //     //     invariant 0 <= i
    //     //     invariant nTemp != null
    //     //     invariant nTemp.Valid()
    //     //     invariant index == |n.Contents| - 1 ==> i >= nTemp.weight - 1
    //     //     invariant index == |n.Contents| - 1 ==> n2 == null
    //     //     invariant n1 == null || n1.Valid()
    //     //     invariant n2 == null || n2.Valid()
    //     //     // invariant n1 != null ==> n1.Valid() && n1.Contents == n.Contents[..nTemp.weight]
    //     //     // invariant n2 != null ==> n2.Valid() && n2.Contents == n.Contents[]
    //     //     invariant 0 <= i < |nTemp.Contents|
    //     //     invariant 0 <= i < nTemp.weight - 1 ==> nTemp.weight > 0
    //     //     // invariant nTemp.weight > 0 ==> nTemp.left != null
    //     //     // invariant nTemp.weight !
    //     //     // invariant 0 <= leftSize <= index <= rightSize < |n.Contents|
    //     //     // invariant n1 != null ==> n1.Valid() && n1.Contents == n.Contents[..leftSize]
    //     //     // invariant n2 != null ==> n2.Valid() && n2.Contents == n.Contents[rightSize..]
    //     //     invariant nTemp.left != null && nTemp.right != null ==> nTemp.left.Repr !! nTemp.right.Repr
    //     //     // invariant i < nTemp.weight && nTemp.right != null ==> nTemp.right.Repr < n2.Repr
    //     //     invariant (n1 != null && n2 != null) ==> n1.Repr !! n2.Repr
    //     //     // invariant 0 <= i - nTemp.weight <= nTemp.weight
    //     //     // invariant n1 != null && n2 != null ==> n
    //     //     decreases nTemp.Repr
    //     // {
    //     //     if (i < nTemp.weight) {
    //     //         // split point lies on the left subtree - so right subtree is part of the second half
    //     //         n2 := concat(nTemp.right, n2);
    //     //         // assert nTemp.left != null && nTemp.right != null ==> nTemp.left.Repr !! nTemp.right.Repr;
    //     //         // if (nTemp.left != null && nTemp.right != null) {
    //     //         //     assert nTem
    //     //         // 
    //     //         if (nTemp.right != null) {
    //     //             rightSize := rightSize - |nTemp.right.Contents| + 1;
    //     //         }
    //     //         // assert nTemp.left != null;
    //     //         // if nTemp.left == null, then it means that nTemp.weight == 0
    //     //         assert nTemp.weight > 0;
    //     //         nTemp := nTemp.left;
    //     //     } else {
    //     //         // split point lies on the right subtree
    //     //         n1 := concat(n1, nTemp.left);
    //     //         if (nTemp.left != null) {
    //     //             leftSize := leftSize + |nTemp.left.Contents|;
    //     //         }
    //     //         i := i - nTemp.weight;
    //     //         nTemp := nTemp.right;
    //     //     }
    //     // }

    //     // // have found the terminal node with the desired split point as nTemp
    //     // if (i == 0) {
    //     //     n2 := concat(nTemp, n2);
    //     // } else if (i == nTemp.weight - 1) {
    //     //     n1 := concat(n1, nTemp);
    //     // } else {
    //     //     // Need to split leaf node into two parts in new tree
    //     //     var splitLeft := new Node.Terminal(nTemp.data[..i]);
    //     //     var splitRight := new Node.Terminal(nTemp.data[i..]);
    //     //     n1 := concat(n1, splitLeft);
    //     //     n2 := concat(splitRight, n2);
    //     // }
    // }
}

