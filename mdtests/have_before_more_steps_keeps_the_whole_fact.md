# An intermediate conjunction keeps the whole fact

`have y > 0 and z == 1;` retains both conjuncts for later written steps,
even when the outer goal needs only `y > 0`.

```c filename=have_before_more_steps_keeps_the_whole_fact.c
void unused(void) {}
```

```click
verifying "have_before_more_steps_keeps_the_whole_fact.c";

theorem t(x: int32, y: int32, z: int32) {
    requires x < y implies (y > 0 and z == 1);
    requires x < y;
    ensures y > 0 by {
        have y > 0 and z == 1;
        have z == 1 by known();
        known();
    }
}
```

```expect
pass
```
