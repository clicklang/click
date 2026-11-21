# Compound read expressions use the store's equation

```c filename=compound.c
int32 word(int32 *p) { *p = 7; return *p + 3; }
uint64 wide(uint64 *p) { *p = 7; return *p + 3; }
```

```click
verifying "compound.c";
int32 word(int32* p) {
    owns p[0..1];
    ensures result == 10;
} by {
    step();
    have *p == 7 by { known(); }
    have *p + 3 == 10 by { rewrite(*p, 7); known(); }
    step_until(function.exit);
}
uint64 wide(uint64* p) {
    owns p[0..1];
    ensures result == 10;
} by {
    step();
    have *p == 7 by { known(); }
    have *p + 3 == 10 by { rewrite(*p, 7); known(); }
    step_until(function.exit);
}
```

```expect
pass
```
