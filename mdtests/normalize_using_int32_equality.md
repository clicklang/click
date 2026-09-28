# Normalization uses explicit int32 equality from the trusted graph

```c filename=int32_equality.c
void keep(int32 a, int32 b, int32 c) { }
```

```click
verifying "int32_equality.c";

void keep(int32 a, int32 b, int32 c) {
    requires a == b;
    requires b == c;
    ensures a == c;
} by {
    execute();
    normalize() using { }
}

theorem choose(a: int32, b: int32, c: int32) {
    requires a == b;
    requires b == c;
    ensures (if c == a { 7 } else { 0 }) == 7 by {
        normalize() using { }
    }
}
```

```expect
pass
```
