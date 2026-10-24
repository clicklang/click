# An untyped `let` of an Integer is an Integer

An untyped `let` has its value's type. `a` below is `to_integer(x)`, so `a`
is an Integer, and `a + 1` and `b * 2` are arithmetic on Integers alone,
which needs no annotation: `b` and `c` are exact Integers too, so `b > x`
holds at `x == INT32_MAX`. The same holds for the lets of a function
contract and for a chain of `let ... ;` inside an expression. A `let` of a
machine value is a machine value, so arithmetic on it is refused
(`mdtests/an_untyped_let_of_a_machine_let_is_refused.md`).

```c filename=identity.c
int32 identity(int32 x) {
    return x;
}
```

```click
verifying "identity.c";

theorem chain(x: int32) {
    let a = to_integer(x);
    let b = a + 1;
    let c = b * 2;
    requires x == 2147483647;
    ensures b > x by auto();
    ensures c == 2 * to_integer(x) + 2 by auto();
}

theorem nested_chain(x: int32) {
    ensures (let a = to_integer(x); let b = a + 1; let c = b * 2; c) == 2 * to_integer(x) + 2
        by auto();
}

int32 identity(int32 x) {
    let a = to_integer(x);
    let b = a + 1;
    ensures to_integer(result) + 1 == b by auto();
}
```

```expect
pass
```
