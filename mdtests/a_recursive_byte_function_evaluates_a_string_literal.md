# A recursive byte function evaluates a string literal

`output_from` copies the bytes of `s` from `k`, counting `remaining` down to
zero, so it returns a list while its measure is an `int32`. The contract
states what `emit` records as `output_from` of its argument, here the
literal `"hi"`, whose `char` is signed. The literal is read as unsigned bytes
and each call is the same term wherever it is written, so proving the output
bottom-up takes one `unfold` and one `close()` per byte.

```c filename=a_recursive_byte_function_evaluates_a_string_literal.c
#include <stdio.h>

int emit(FILE *file, const char *format);

int greet(FILE *file)
{
    return emit(file, "hi");
}
```

```click
verifying "a_recursive_byte_function_evaluates_a_string_literal.c";
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
        WriteAttempt::Attempt(b"hi", result), old(out.write_history));
} by {
    step();
    have output_from("a_recursive_byte_function_evaluates_a_string_literal.c"::greet.string_literal(0), 2u64, 0) == List::Nil by {
        unfold(output_from("a_recursive_byte_function_evaluates_a_string_literal.c"::greet.string_literal(0), 2u64, 0));
        close();
    }
    have output_from("a_recursive_byte_function_evaluates_a_string_literal.c"::greet.string_literal(0), 1u64, 1) == b"i" by {
        unfold(output_from("a_recursive_byte_function_evaluates_a_string_literal.c"::greet.string_literal(0), 1u64, 1));
        close();
    }
    have output_from("a_recursive_byte_function_evaluates_a_string_literal.c"::greet.string_literal(0), 0u64, 2) == b"hi" by {
        unfold(output_from("a_recursive_byte_function_evaluates_a_string_literal.c"::greet.string_literal(0), 0u64, 2));
        close();
    }
    step();
}
```

```expect
pass
```
