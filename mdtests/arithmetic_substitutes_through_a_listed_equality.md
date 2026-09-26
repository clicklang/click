# `arithmetic()` substitutes an atom through a listed equality

`y == x` and `0 <= x` give `0 <= y`: the certificate weakens the equality to
the direction `x - y <= 0` and adds it to `-x <= 0`, both steps the kernel's
signed-arithmetic checker already verifies. The planner's two-premise search
used to pair only inequalities, so neither orientation of the equality could
be used and the listed premises were reported insufficient.

```c filename=arithmetic_substitutes_through_a_listed_equality.c
int32 same(int32 x, int32 y) {
    return 0;
}
```

```click
verifying "arithmetic_substitutes_through_a_listed_equality.c";

int32 same(int32 x, int32 y) {
    requires y == x;
    requires 0 <= x;
    requires x < 10;
    ensures result == 0;
} by {
    have 0 <= y by { arithmetic() using { y == x; 0 <= x; } }
    have y >= 0 by { arithmetic() using { x == y; 0 <= x; } }
    have y < 10 by { arithmetic() using { x < 10; y == x; } }
    step();
    simp();
}
```

```expect
pass
```
