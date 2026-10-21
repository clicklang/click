# `arithmetic` reads a negated order premise as the reverse order

`not (a >= b)` is the same ordered pair as `a < b`. A certificate that adds it
to another bound prints the sum of the pair, and the check reads the negated
premise as that pair, so the sum is accepted as it is for `a < b`. Here the
sum with `b`'s `int32` range shows `a + 1` defined.

```click
theorem successor_below(a: int32, b: int32) {
    requires not (a >= b);

    ensures a + 1 <= b by {
        arithmetic() using {
            not (a >= b);
        };
    }
}
```

```expect
pass
```

A loop whose exit test is stored in a local relies on this
([`a_stored_break_test_closes_the_back_edge.md`](a_stored_break_test_closes_the_back_edge.md)).
