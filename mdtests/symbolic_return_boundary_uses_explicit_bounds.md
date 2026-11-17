# A symbolic returned range uses explicit endpoint bounds

The caller retains a disjoint constant range while unpacking a symbolic one.
Direct bounds on the returned endpoint give a disjoint enclosing interval;
checking that boundary needs no order-chain or pointer-alias discovery.

```c filename=symbolic_return_boundary.c
void unbox(int32* p, int32 n);
void forward(int32* p, int32 n) { unbox(p, n); }
```

```click
resource packed(p: int32*, n: int32) {
    owns p[0..n];
}

verifying "symbolic_return_boundary.c";
extern void unbox(int32* p, int32 n) {
    consumes packed(p, n);
    produces p[0..n];
}
void forward(int32* p, int32 n) {
    requires 0 < n;
    requires n <= 4;
    consumes packed(p, n);
    owns p[8..12];
    produces p[0..n];
}
```

```expect
pass
```
