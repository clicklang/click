# Int32 addition congruence in the trusted equality graph

```c filename=int32_addition.c
void keep(int32 a, int32 b, int32 c) { }
```

```click
verifying "int32_addition.c";

void keep(int32 a, int32 b, int32 c) {
    requires a == b;
    requires defined(a + c);
    requires defined(b + c);
    ensures to_integer(a + c) == to_integer(b + c);
} by {
    step_until(function.exit);
    normalize() using { };
}

theorem offsets(p: int32*, a: int32, b: int32, c: int32) {
    requires a == b;
    requires defined(a + c);
    requires defined(b + c);
    ensures p + (a + c) == p + (b + c) by {
        normalize() using { };
    }
}

theorem choose(a: int32, b: int32, c: int32) {
    requires a == b;
    requires defined(a + c);
    requires defined(b + c);
    ensures (if to_integer(a + c) == to_integer(b + c) { 7 } else { 0 }) == 7 by {
        normalize() using { };
    }
}
```

```expect
pass
```
