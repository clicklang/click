# transport using names its source and target

A refused `transport ... using` in a pure theorem prints its source and target
with the theorem's parameter names, so the two claims read apart.

```c filename=transport_using_names_its_source_and_target.c
void unused(void) {}
```

```click
verifying "transport_using_names_its_source_and_target.c";

theorem t(a: int32, b: int32) {
    requires a == 1;
    ensures b == 1 by {
        transport(a == 1, b == 1) using { a == 1; };
    }
}
```

```expect
fail: `transport using` target does not follow from the source fact and the listed premises
  source: a == 1
  target: b == 1
```
