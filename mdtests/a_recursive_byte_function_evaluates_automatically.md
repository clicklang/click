# A recursive byte function evaluates automatically

`emit` records `output_from` of its format, a recursion that counts an
`int32` measure down while it copies bytes. The implicit proof of `greet`
evaluates it over the literal: it unfolds each call whose measure is a
constant, entering the `if` arm that constant selects, for as many steps as
the measure takes. The thirteen bytes of `"hello, world\n"` need no written
proof.

```c filename=a_recursive_byte_function_evaluates_automatically.c
#include <stdio.h>

int emit(FILE *file, const char *format);

int greet(FILE *file)
{
    return emit(file, "hello, world\n");
}
```

```click
verifying "a_recursive_byte_function_evaluates_automatically.c";
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
        WriteAttempt::Attempt(b"hello, world\n", result), old(out.write_history));
}
```

```expect
pass
```
