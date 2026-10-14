# a contract's owned memory is its write footprint

This checks that a function may write exactly the ranges its contract owns —
a symbolic range through each of two array parameters and one cell through a
pointer — and that the writes land.

```c filename=contract_owns_write_footprint.c
int32 contract_owns_write_footprint(int32 p[], int32 dst[], int32* counter, int32 n) {
    p[0] = 1;
    dst[0] = 2;
    counter[0] = n;
    return 0;
}
```

```click
verifying "contract_owns_write_footprint.c";

int32 contract_owns_write_footprint(int32 p[], int32 dst[], int32* counter, int32 n) {
    requires n >= 1 and n <= 100;
    owns p[0..n];
    owns dst[0..n];
    owns counter[0..1];
    ensures writes_first: p[0] == 1;
    ensures writes_second: dst[0] == 2;
    ensures writes_counter: counter[0] == n;
} by { execute(); simp(); }
```

```expect
pass
```
