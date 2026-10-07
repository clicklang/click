# a predicate reading a global by name is refused

The predicate form of
`mdtests/a_pure_function_reading_a_global_by_name_is_refused.md`: a predicate
fact is keyed on its arguments, so `counter_is(5)` would be one fact across
the store to `counter` and the false `ensures` would be discharged by the
`requires`. The body is refused before any contract is lowered.

```c filename=bump.c
int32 counter = 1;

int32 bump() {
    counter = counter + 1;
    return counter;
}
```

```click
verifying "bump.c";

predicate counter_is(v: int32) {
    counter == v
}

int32 bump() {
    owns &counter[0..1];
    requires counter == 5;
    requires counter_is(5);
    ensures counter == 6;
    ensures counter_is(5);
} by {
    execute();
    simp();
}
```

```expect
fail: predicate `counter_is` reads the C object `counter` by name
```
