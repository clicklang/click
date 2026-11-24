# A long recursion over constants is evaluated one level at a time

`emit` records `output_from` of its sixty-byte format. The implicit proof
evaluates the call one level at a time: each level is a `have` that one call
equals the arm its constant guards select, proved by `unfold` and `close()`,
all inside one `have` for the call's value, so the work grows linearly with
the measure and the goal is read once at the end.

```c filename=a_long_recursion_over_constants_is_evaluated_one_level_at_a_time.c
#include <stdio.h>

int emit(FILE *file, const char *format);

int greet(FILE *file)
{
    return emit(file, "012345678901234567890123456789012345678901234567890123456789");
}
```

```click
verifying "a_long_recursion_over_constants_is_evaluated_one_level_at_a_time.c";
import click::c::stdio::{stream, write_requests};

function output_from(s: uint8[], k: uint64, remaining: int32) -> List<uint8>
    decreases remaining
{
    if remaining <= 0 {
        List<uint8>::Nil
    } else {
        List<uint8>::Cons(s[k], output_from(s, k + 1u64, remaining - 1))
    }
}

extern int32 emit(FILE* file, const uint8* format) {
    let n: uint64;
    views click::c::string::cstr_at(format, n);
    requires n <= 2147483647u64;
    owns out: stream(file);
    ensures out.write_history == List::Cons(
        WriteAttempt::Attempt(output_from(format, 0u64, n as int32), result),
        old(out.write_history));
}

int32 greet(FILE* file) {
    owns out: stream(file);
    ensures out.write_history == List::Cons(
        WriteAttempt::Attempt(b"012345678901234567890123456789012345678901234567890123456789", result), old(out.write_history));
}
```

```expect
pass
```
