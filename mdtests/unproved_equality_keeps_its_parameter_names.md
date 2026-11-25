# An unproved equality keeps its parameter names

The premise `a == 1` cannot prove the unrelated goal `b == 1`. Ordinary
fact checking refuses the goal and prints both the available premise and
the unproved goal with their distinct parameter names.

```c filename=unproved_equality_keeps_its_parameter_names.c
void unused(void) {}
```

```click
verifying "unproved_equality_keeps_its_parameter_names.c";

theorem t(a: int32, b: int32) {
    requires a == 1;
    ensures b == 1 by {
        close();
    }
}
```

```expect
fail: could not establish `b == 1`
```
