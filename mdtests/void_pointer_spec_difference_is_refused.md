# Two `void *` are not subtracted in a spec

A spec steps a `void *` by an offset, but does not take the difference of
two: cast both to a typed pointer first.

```c filename=void_pointer_spec_difference_is_refused.c
void *same(void *q) {
    return q;
}
```

```click
verifying "void_pointer_spec_difference_is_refused.c";

void *same(void *q) {
    ensures result - q == 0;
}
```

```expect
fail: a `void *` has no pointee type; cast it to a typed pointer or use `load<T>`
```
