# A theorem application in a function proof keeps every conclusion

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
    ensures x >= 0 by { unfold(small(x)); close(); }
    ensures x <= 10 by { unfold(small(x)); close(); }
}

theorem needs_upper(x: int32) {
    requires x <= 10;
    ensures x <= 20 by close();
}

int32 ident(int32 x) {
    requires small(x);

    ensures result >= 0 by {
        have x >= 0 by {
            apply(two_bounds(x));
            apply(needs_upper(x));
            close();
        }
    }
}
```

```expect
pass
```
