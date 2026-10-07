# A return narrowing in range verifies

The positive of
`mdtests/a_refuted_return_narrowing_names_its_range_and_value.md`: `x == 44`
puts the returned `int32` inside the `uint8` range. The bounds the kernel
files at the function's exit are derived from the proof's facts the way a
statement's prerequisite is under `execute()`, so a fact that implies a bound
discharges it; an exact `x >= 0` and `x <= 255` is not required.

```c filename=a_return_narrowing_in_range_verifies.c
uint8 f(int32 x) { return x; }
```

```click
verifying "a_return_narrowing_in_range_verifies.c";

uint8 f(int32 x) {
    requires x == 44;
    ensures result == 44;
} by { execute(); simp(); }
```

```expect
pass
```
