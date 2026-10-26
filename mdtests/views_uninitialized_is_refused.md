# `views uninitialized(...)` is refused

A viewed range is only read, so a view of bytes with no claim to be
initialized could never be used. `uninitialized(...)` is accepted only in an
owning clause: `owns`, `consumes`, or `produces`.

```c filename=uninitialized_view.c
int get(const int *p) { return *p; }
```

```click
verifying "uninitialized_view.c";

int32 get(const int32* p) {
    views uninitialized(p[0..1]);
    ensures true;
} by { execute(); solve(); }
```

```expect
fail: a viewed range is read, so its bytes are initialized
```
