# An addition theorem needs the outer sum to be defined

```c filename=omitted_guard.c
int32 probe(int32 a, int32 b, int32 c) { return 0; }
```

```click
verifying "omitted_guard.c";

theorem add_observation(left: int32, right: int32) {
    requires defined(left + right);
    ensures to_integer(left + right) == to_integer(left) + to_integer(right);
}

int32 probe(int32 a, int32 b, int32 c) {
    requires defined(a + b);
    ensures result == 0;
} by {
    apply(add_observation(a + b, c));
}
```

```expect
fail: theorem `add_observation` has an unproved obligation
```
