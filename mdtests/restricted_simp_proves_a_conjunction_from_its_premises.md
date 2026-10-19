# a restricted simp proves a conjunction from its listed premises

`simp() using { ... }` proves a conjunction one conjunct at a time, each from
the same listed premises, and then closes the conjunction from the conjuncts.
Each conjunct here needs a listed premise, and `result == i` follows from the
returned value.

```c filename=checked_index.c
int32 checked_index(int32 i, int32 n) {
    return i;
}
```

```click
verifying "checked_index.c";

int32 checked_index(int32 i, int32 n) {
    requires i >= 0;
    requires i < n;
    ensures in_range: 0 <= i and i < n and result == i by {
        execute();
        have 0 <= i and i < n and result == i by {
            simp() using {
                i >= 0;
                i < n;
            };
        }
    }
}
```

```expect
pass
```
