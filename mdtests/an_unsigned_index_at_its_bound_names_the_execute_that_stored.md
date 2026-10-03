# An unsigned index at its bound names the `execute()` that stored

`mdtests/an_unsigned_index_at_its_bound_is_refused.md` over a local array.
`x <= 4u` admits the one-past element `values[4]`, which the store may
write. The proof wrote `execute()`, which advances statement by statement;
the refusal names that tactic, where it used to name a `step()` the proof
never wrote.

```c filename=an_unsigned_index_at_its_bound_names_the_execute_that_stored.c
int32 write_local(uint32 x) {
    int32 values[4] = {1, 2, 3, 4};
    if (x <= 4u) {
        values[x] = 7;
    }
    return values[0];
}
```

```click
verifying "an_unsigned_index_at_its_bound_names_the_execute_that_stored.c";

int32 write_local(uint32 x) {
    ensures result == result;
} by {
    execute();
    simp();
}
```

```expect
fail: `execute()` is missing prerequisite
```
