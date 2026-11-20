# Check a signed order chain with explicit premises

Each written premise contributes one link. A strict literal gap between two
links also supplies strictness.

```click
theorem explicit_chain(a: int32, b: int32, c: int32, d: int32) {
    requires a <= b;
    requires b < c;
    requires c <= d;
    ensures a < d by {
        order_chain() using { a <= b; b < c; c <= d; };
    }
}

theorem explicit_chain_through_literals(a: int32, b: int32) {
    requires a <= 1;
    requires 2 <= b;
    ensures a < b by {
        order_chain() using { a <= 1; 2 <= b; };
    }
}
```

```expect
pass
```
