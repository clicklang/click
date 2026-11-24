# A sign disjunction can exclude zero without excluding minus one

```c filename=arithmetic.c
int32 divide(int32 n, int32 d) { return n / d; }
```

```click
verifying "arithmetic.c";
int32 divide(int32 n, int32 d) {
    requires d > 0 or d < 0;
    ensures true;
}
```

```expect
fail: INT_MIN / -1
```
