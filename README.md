# An implementation of Rope in Dafny
## Requirements
Dafny `>= 4.0`
## Quickstart

To use the library in Dafny, simply include the file in your project. Common
functions to use are listed below:

```dafny
include "Rope.dfy"
import opened Rope

// initializing
var n1: Rope := new Rope.Terminal("Hello ");
var n2: Rope := new Rope.Terminal("world!");

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

// substring: returns a Rope
var first: Rope := Rope.substring(n, 0, 5);
var firstStr: string := first.toString();
assert firstStr == "Hello";
```
