# A refuted return narrowing names its range and value

Returning an `int32` from a `uint8` function owes `0 <= x <= 255`. With
`x == 300` the upper bound is false, and the refusal says so: it names the
conversion's bound, the condition it owes, and the fact that refutes it. The
conversion files the refuted bound as the obligation it is, instead of
refusing the value as a `type mismatch`; both the published path and its
checked trace then return, and the proof object no longer reports "a
published path outcome is not its trace's outcome" where the surface's
richer context had refuted what the trace's exact context filed.
`mdtests/a_return_narrowing_in_range_verifies.md` is the positive.

```c filename=a_refuted_return_narrowing_names_its_range_and_value.c
uint8 f(int32 x) { return x; }
```

```click
verifying "a_refuted_return_narrowing_names_its_range_and_value.c";

uint8 f(int32 x) {
    requires x == 300;
    ensures result == 44;
} by { execute(); simp(); }
```

```expect
fail: uint8 narrowing upper bound: the facts refute `x <= 255`: [x == 300]
```
