# A built-in check accepts the Integer reading of its condition

Specification arithmetic is Integer, so a `requires` or `have` records its
Integer reading. A signed definedness check holds exactly when both Integer
bounds of the exact result do: `int32` `a - b` is defined once
`to_integer(a) - to_integer(b)` lies in `int32`, in either spelling of each
bound. A native comparison through an in-range machine operation is its
Integer reading: `a <= 4294967295u32 - b` is recorded as
`to_integer(a) <= 4294967295 - to_integer(b)`, and the C branch on the native
comparison is decided by it, since `4294967295u32 - b` cannot wrap. The
Rust addition panic check reads the same way
(`charon_refused_panic_check_names_its_condition` in `tests/rust_import.rs`).

```c filename=integer_reading.c
int difference(int a, int b) { return a - b; }

int difference_low_first(int a, int b) { return a - b; }

unsigned fits(unsigned a, unsigned b) {
    if (a <= 4294967295u - b) {
        return 1;
    }
    return 0;
}
```

```click
verifying "integer_reading.c";

int32 difference(int32 a, int32 b) {
    requires to_integer(a) - to_integer(b) <= 2147483647;
    requires to_integer(a) - to_integer(b) >= -2147483648;
    ensures to_integer(result) == to_integer(a) - to_integer(b);
}

int32 difference_low_first(int32 a, int32 b) {
    requires -2147483648 <= to_integer(a) - to_integer(b);
    requires 2147483647 >= to_integer(a) - to_integer(b);
    ensures to_integer(result) == to_integer(a) - to_integer(b);
}

uint32 fits(uint32 a, uint32 b) {
    requires a <= 4294967295u32 - b;
    ensures result == 1u32;
}

theorem a_difference_in_range_is_defined(a: int32, b: int32) {
    requires to_integer(a) - to_integer(b) >= -2147483648;
    requires to_integer(a) - to_integer(b) <= 2147483647;
    ensures defined(a - b);
}
```

```expect
pass
```
