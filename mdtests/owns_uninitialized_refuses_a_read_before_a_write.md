# `owns uninitialized(...)` refuses a read before a write

A callee that owns `uninitialized(p[0..1])` holds `*p` with no claim that it
is initialized. Its proof starts with the byte unwritten, as a fresh local's
is, so reading `*p` before writing it is a read of uninitialized storage. The
positive case is
[`owns_uninitialized_reads_what_it_wrote.md`](owns_uninitialized_reads_what_it_wrote.md).

```c filename=uninitialized_get.c
int get(int *p) { return *p; }
```

```click
verifying "uninitialized_get.c";

int32 get(int32* p) {
    owns uninitialized(p[0..1]);
    ensures true;
}
```

```expect
fail: read of uninitialized storage
```
