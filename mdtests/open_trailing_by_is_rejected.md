# Open uses in-block proofs for restoration

```c filename=open_by_superfluous.c
void set(int32* p, int32 x) { p[0] = x; }
```

```click
resource cell(p: int32*) { owns p[0..1]; fact p[0] > 0; }
verifying "open_by_superfluous.c";
void set(int32* p, int32 x) {
    requires x > 0;
    owns cell(p);
} by {
    open(cell(p)) { } by { solve(); }
    solve();
}
```

```expect
fail: `open` takes no trailing `by`
```
