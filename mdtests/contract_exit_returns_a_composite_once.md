# A contract exit returns a held composite once

Control for the duplicate-return refusals: a function that holds `wrap(p)`
and returns exactly it verifies.

```c filename=composite_once.c
int32 f(int32* p) {
    return 0;
}
```

```click
resource wrap(p: int32*) {
    owns p[0..1];
}
verifying "composite_once.c";
int32 f(int32* p) {
    owns wrap(p);
} by auto;
```

```expect
pass
```
