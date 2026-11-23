# A single counterexample refutes a universal

`not (forall ...)` lowers to an existential counterexample. Giving `1` as
the witness leaves the concrete comparison `1 != 0`.

```c filename=a_step_after_instantiate_refutes_an_introduced_universal.c
void unused(void) {}
```

```click
verifying "a_step_after_instantiate_refutes_an_introduced_universal.c";

theorem not_all_zero(n: int32) {
    ensures not (forall (x: int32) { x == 0 }) by {
        witness(1);
        normalize();
    }
}
```

```expect
pass
```
