# `fprintf` ignores arguments its format does not convert

C evaluates and ignores the arguments a format does not convert (C11
7.21.6.1p2). The format `"a%%b"` converts none, so the `int` argument is
ignored and the stream records `a%b`.

```c filename=fprintf_ignores_arguments_its_format_does_not_convert.c
#include <stdio.h>

int report(FILE *file, int value)
{
    return fprintf(file, "a%%b", value);
}
```

```click
verifying "fprintf_ignores_arguments_its_format_does_not_convert.c";
import click::c::stdio::{stream};

int32 report(FILE* file, int32 value) {
    owns out: stream(file);
    ensures result == 3 or result < 0;
    ensures out.write_history == List::Cons(
        WriteAttempt::Attempt(b"a%b", result), old(out.write_history));
}
```

```expect
pass
```
