# Case elimination proves a focused fact before and after execution

`cases` proves the proposition opened by `have`; execution continues after
that fact has been established in every disjunct.

```c filename=focused-cases.c
int32 before(int32 n) { return n; }
int32 after(int32 n) { return n; }
```

```click
verifying "focused-cases.c";
int32 before(int32 n) {
    requires n == 0 or n == 1;
    ensures 0 <= result;
    ensures result <= 1;
} by {
    have 0 <= n by {
        cases { n == 0 => { solve(); } n == 1 => { solve(); } }
    }
    have n <= 1 by {
        cases { n == 0 => { solve(); } n == 1 => { solve(); } }
    }
}
int32 after(int32 n) {
    requires n == 0 or n == 1;
    ensures 0 <= result;
    ensures result <= 1;
} by {
    step_until(function.exit);
    have 0 <= result by {
        cases { n == 0 => { solve(); } n == 1 => { solve(); } }
    }
    have result <= 1 by {
        cases { n == 0 => { solve(); } n == 1 => { solve(); } }
    }
    solve();
}
```

```expect
pass
```
