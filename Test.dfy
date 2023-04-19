include "Rope.dfy"
import opened Rope

method test()
{
    var n := new Node.Terminal("Hello ");
    assert n.Valid() && n.weight == 6 && n.data == "Hello " && n.Repr == {n} && n.Contents == "Hello ";
    var n1 := new Node.Terminal("my ");
    assert n1.Valid() && n1.Repr !! n.Repr;
    var n2 := concat(n, n1);
    assert n2.Contents == "Hello my " && n2.left == n && n2.right == n1 && n2.weight == |n.Contents|;
    var n3 := new Node.Terminal("na");
    assert n3.weight == 2;
    var n4 := new Node.Terminal("me i");
    var n5 := concat(n3, n4);
    assert n5.weight == 2;
    var n6 := new Node.Terminal("s");
    var n7 := new Node.Terminal(" Simon");
    var n8 := concat(n6, n7);
    var n9 := concat(n5, n8);
    var B := concat(n2, n9);
    assert B.weight == 9 && B.Contents == "Hello my name is Simon";
    var AHopeful := concat(B, null);
    assert AHopeful == B;
    assert AHopeful.weight == 9;
    assert AHopeful.Contents == B.Contents;

    var foo := delete(AHopeful, 0, 1);
    assert foo.Contents == "ello my name is Simon";
    var s := foo.report(1,3);
    assert s == "ll";
    print s;
}

