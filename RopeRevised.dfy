include "Utils.dfy"

module Rope {
    import opened Utils

    const leafLen := 5;

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
                Contents == data &&
                weight == |data| &&
                data != [] &&
                |data| <= leafLen) &&
                // forall i :: 0 <= i < |data| ==> data[i] !in {' ', '\n'/*, '\f'*/, '\r', '\t'/*, '\v'*/}) &&
            (left != null && right == null ==>
                Contents == left.Contents &&
                weight == |left.Contents| &&
                data == []) &&
            (left == null && right != null ==>
                Contents == right.Contents &&
                weight == 0 &&
                data == []) &&
            (left != null && right != null ==>
                left.Repr !! right.Repr &&
                Contents == left.Contents + right.Contents &&
                weight == |left.Contents| &&
                data == [])
        }

        function getWeightsOfAllRightChildren(): nat
            reads right, Repr
            requires Valid()
            decreases Repr
        {
            if right == null then 0 else right.weight + right.getWeightsOfAllRightChildren()
        } 

        constructor Init(x: string)
            requires x != []
            decreases x
            ensures Valid() && fresh(Repr)
        { 
            if (|x| <= leafLen) {
                data := x;
                weight := |x|;
                left := null;
                right := null;
                Contents := x;
                Repr := {this};
            } else {
                var strLeft := x[..|x|/2];
                var strRight := x[|x|/2..];
                data := [];

                var l: Node;
                var r: Node;
                l := new Node.Init(strLeft);
                r := new Node.Init(strRight);
                Repr := {this} + l.Repr + r.Repr;
                Contents := x;
                left := l;
                right := r;
                weight := l.weight + l.getWeightsOfAllRightChildren();
            }
        }   

    }
}