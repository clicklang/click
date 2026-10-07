# a pure function reading a qualified global is refused

`mdtests/a_pure_function_reading_a_global_by_name_is_refused.md` through the
qualified spelling `bump::counter`. The qualified form lowers to a load of
the object's storage directly, so it reads the ambient memory exactly as the
bare name does and is refused the same way; a function-local static named
through `unit::function::name` is a qualified object as well.

```c filename=bump.c
int32 counter = 1;

int32 bump() {
    counter = counter + 1;
    return counter;
}
```

```click
verifying "bump.c" as bump;

function read_counter(x: int32) -> int32 {
    bump::counter + x
}

int32 bump() {
    owns &counter[0..1];
    requires counter == 5;
    requires read_counter(0) == 5;
    ensures counter == 6;
    ensures read_counter(0) == 5;
} by {
    execute();
    simp();
}
```

```expect
fail: pure function `read_counter` reads the C object `bump::counter` by name
```
