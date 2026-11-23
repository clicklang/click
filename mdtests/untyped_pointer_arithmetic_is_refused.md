# Arithmetic on a `Pointer` is refused

A `Pointer` has no pointee type, so `q + 1` has no element width to step by.
A pure function's `Pointer` parameter is refused in arithmetic, also inside a
typed load's address; `byte_offset(q, n)` states the step in bytes.

```c filename=untyped_pointer_arithmetic.c
int32 first(int32 *p) {
    return p[0];
}
```

```click
verifying "untyped_pointer_arithmetic.c";

function second(q: Pointer) -> int32 { load<int32>(q + 1) }

int32 first(int32 *p) {
    views p[0..2];
    ensures result == second(p) - second(p) + p[0];
}
```

```expect
fail: a `Pointer` has no pointee type; cast it to a typed pointer or use `load<T>`
```
