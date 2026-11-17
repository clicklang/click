# Symbolic output partitions rejoin a retained frame

Flat outputs and constructed children retain their checked partition. Both
cross a call beside a disjoint retained range; the two symbolic output pieces
do not need their separation rediscovered during caller admission.

```c filename=symbolic_output_partitions.c
void split_flat(int32* p, int32 n);
void split_box(int32* p, int32 n);
void forward_flat(int32* p, int32 n) { split_flat(p, n); }
void forward_box(int32* p, int32 n) { split_box(p, n); }
```

```click
resource split(p: int32*, n: int32) {
    owns p[0..n];
    owns p[n..8];
}
verifying "symbolic_output_partitions.c";
extern void split_flat(int32* p, int32 n) {
    requires 1 <= n;
    requires n <= 4;
    consumes p[0..8];
    produces p[0..n];
    produces p[n..8];
}
extern void split_box(int32* p, int32 n) {
    requires 1 <= n;
    requires n <= 4;
    consumes p[0..8];
    produces split(p, n);
}
void forward_flat(int32* p, int32 n) {
    requires 1 <= n;
    requires n <= 4;
    consumes p[0..8];
    owns p[16..20];
    produces p[0..n];
    produces p[n..8];
}
void forward_box(int32* p, int32 n) {
    requires 1 <= n;
    requires n <= 4;
    consumes p[0..8];
    owns p[16..20];
    produces split(p, n);
}
```

```expect
pass
```
