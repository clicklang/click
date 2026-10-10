# An empty resource-free loop clause still certifies a loop rule

The loop clause has no invariants, measures, or resource-frame checks. Its
checked rule must still be applied instead of unrolling the polling loop.

```c filename=r.c
int poll(int x) { return x; }
int spin(int x) {
    while (poll(x) == 0) { }
    return 1;
}
```

```click
verifying "r.c";
int32 poll(int32 x) {
    ensures result == x;
} by { step(); simp(); }
int32 spin(int32 x) diverges {
    ensures result == 1;
} by {
    loop diverges { }
    step();
    simp();
}
```

```expect
pass
```
