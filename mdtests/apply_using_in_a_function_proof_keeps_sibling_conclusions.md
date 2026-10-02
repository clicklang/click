# apply using in a function proof keeps every conclusion

The `have` body below applies `two_bounds`, whose first guarantee is the
`have` goal itself, and then cites its second guarantee `x <= 10` as the
listed premise of another application. The explicit application adds both
guarantees whichever one the goal happens to be.

```c filename=ident.c
int32 ident(int32 x) {
    return x;
}
```

```click
verifying "ident.c";

predicate small(x: int32) {
    x >= 0 and x <= 10
}

theorem two_bounds(x: int32) {
    requires small(x);
    ensures x >= 0 by { unfold(small); simp(); }
    ensures x <= 10 by { unfold(small); simp(); }
}

theorem needs_upper(x: int32) {
    requires x <= 10;
    ensures x <= 20 by { simp(); }
}

int32 ident(int32 x) {
    requires small(x);

    ensures result >= 0 by {
        have x >= 0 by {
            apply(two_bounds(x)) using { small(x); }
            apply(needs_upper(x)) using { x <= 10; }
            assumption();
        }
        execute();
        simp();
    }
}
```

```expect
pass
```
