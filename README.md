# An implementation of Rope in Dafny
## Requirements
Dafny version `>= 4.0` is required.

In Visual Studio Code, you can change the Dafny version by going to the Extensions pane (Ctrl + Shift + X), searching for the 'Dafny' extension, going to Extension Settings, setting 'Dafny: Version' to 4.0 and restarting Visual Studio Code.

## Quickstart

To use the Rope library in Dafny, simply include the `Rope.dfy` file in your project. Common
methods to use and examples of their intended behaviour are listed in the `Test.dfy` file. A snippet of the same is presented below:

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

Note that the `test` method in `Test.dfy` occasionally takes longer than 20 seconds to verify due to the large size of the Rope data structure being built as well as the large number of `assert` statements and their level of detail. In the case this happens, restarting Visual Studio Code, commenting out a few of the assertional statements, or reducing the number of Rope operations used should speed up verification.

Additionally, while both the `concat` method and the `NonTerminal` constructor can be be used to build larger ropes from smaller blocks and are both directly accessible from the `Rope` class, we recommend using the `concat` method since it wraps the `NonTerminal` constructor and is also able to handle `null` as input. 
