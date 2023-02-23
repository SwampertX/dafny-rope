module Utils {
    export provides max, min

    function method max(a: nat, b: nat): nat
        ensures max(a, b) == a || max(a, b) == b
        ensures max(a, b) >= a && max(a, b) >= b
    {
        if a > b then a else b
    }

    function method min(a: nat, b: nat): nat
        ensures min(a, b) == a || min(a, b) == b
        ensures min(a, b) <= a && min(a, b) <= b
    {
        if a < b then a else b
    }
}