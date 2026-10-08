# a pure function takes a global's value as an argument

The positive twin of
`mdtests/a_pure_function_reading_a_global_by_name_is_refused.md` and
`mdtests/a_predicate_reading_a_global_by_name_is_refused.md`: the body reads
only its parameters and the contract passes `counter` in. The application at
entry, `read_counter(counter, 0)`, and the one at exit over the entry value,
`read_counter(old(counter), 0)`, are the same term, so the `requires` fact
discharges the `ensures`; an application over the exit value would be a
different term.

```c filename=bump.c
int32 counter = 1;

int32 bump() {
    counter = counter + 1;
    return counter;
}
```

```click
verifying "bump.c";

function read_counter(c: int32, x: int32) -> int32 {
    c + x
}

predicate counter_is(c: int32, v: int32) {
    c == v
}

int32 bump() {
    owns counter;
    requires counter == 5;
    requires read_counter(counter, 0) == 5;
    requires counter_is(counter, 5);
    ensures counter == 6;
    ensures read_counter(old(counter), 0) == 5;
    ensures counter_is(old(counter), 5);
} by {
    execute();
    simp();
}
```

```expect
pass
```
