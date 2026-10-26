# `owns uninitialized(...)` with a symbolic length refuses a read

The range `p[0..n]` has a length known only at the call. Every element of it
starts unwritten in the callee's proof, so reading `p[n - 1]` before writing
it is a read of uninitialized storage.

```c filename=uninitialized_symbolic_get.c
int get_last(int *p, int n) { return p[n - 1]; }
```

```click
verifying "uninitialized_symbolic_get.c";

int32 get_last(int32* p, int32 n) {
    requires 1 <= n;
    owns uninitialized(p[0..n]);
    ensures true;
}
```

```expect
fail: read of uninitialized storage
```
