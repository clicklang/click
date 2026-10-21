# extract before more steps keeps the whole fact

`extract(y > 0 and z == 1)` closes the goal `y > 0`. Later written steps are
still checked, and they see the whole extracted fact: `z == 1` is available,
not only the part that was the goal.

```c filename=extract_before_more_steps_keeps_the_whole_fact.c
void unused(void) {}
```

```click
verifying "extract_before_more_steps_keeps_the_whole_fact.c";

theorem t(x: int32, y: int32, z: int32) {
    requires x < y implies (y > 0 and z == 1);
    requires x < y;
    ensures y > 0 by {
        extract(y > 0 and z == 1);
        have z == 1 by assumption();
        assumption();
    }
}
```

```expect
pass
```
