include "Rope.dfy"
import opened Rope

method quickstart()
{
    // initializing
    var n1: Rope := new Rope.Terminal("Hello");
    var n2: Rope := new Rope.Terminal(" world!");
    // concat
    var n: Rope := Rope.concat(n1, n2);
    assert n.Valid();
    // toString
    var nstr: string := n.toString();
    assert nstr == "Hello world!";
    // length
    assert n.length() == |nstr|;
    // getCharAtIndex
    var c: char := n.getCharAtIndex(n.length() - 1);
    assert c == '!';
    // report: returns a string
    var fstr: string := n.report(0, 5);
    assert fstr == "Hello";
    // insert: returns a rope
    var n3: Rope := new Rope.Terminal(", beautiful");
    var n4: Rope := Rope.insert(n, n3, 5);
    var n4Str: string := n4.toString();
    assert n4Str == "Hello, beautiful world!";
    // substring: returns a Rope
    var first: Rope := Rope.substring(n, 0, 5);
    var firstStr: string := first.toString();
    assert firstStr == "Hello";
    // delete: returns a Rope
    var second: Rope := Rope.delete(n, 0, 5);
    var secondStr: string := second.toString();
    assert secondStr == " world!";
}

method test()
{
    var n := new Rope.Terminal("Hello ");
    assert n.Valid() && n.weight == 6 && n.data == "Hello " && n.Repr == {n} && n.Contents == "Hello ";
    var n1 := new Rope.Terminal("my ");
    assert n1.Valid() && n1.Repr !! n.Repr;
    var n2 := Rope.concat(n, n1);
    assert n2.Contents == "Hello my " && n2.left == n && n2.right == n1 && n2.weight == |n.Contents|;
    var n3 := new Rope.Terminal("na");
    assert n3.weight == 2;
    var n4 := new Rope.Terminal("me i");
    var n5 := Rope.concat(n3, n4);
    assert n5.weight == 2;
    var n6 := new Rope.Terminal("s");
    var n7 := new Rope.Terminal(" Simon");
    var n8 := Rope.concat(n6, n7);
    var n9 := Rope.concat(n5, n8);
    var B := Rope.concat(n2, n9);
    assert B.weight == 9 && B.Contents == "Hello my name is Simon";
    var AHopeful := Rope.concat(B, null);
    assert AHopeful == B;
    assert AHopeful.weight == 9;
    assert AHopeful.Contents == B.Contents;

    var foo := Rope.delete(AHopeful, 0, 1);
    assert foo.Contents == "ello my name is Simon";
    var s := foo.report(1,3);
    assert s == "ll";
    print s;
}