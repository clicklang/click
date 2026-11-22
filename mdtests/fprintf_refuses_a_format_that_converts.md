# `fprintf` refuses a format that converts an argument

Click models an `fprintf` format of ordinary characters and `%%`. Its
contract requires `click::c::stdio::literal_format` of the format, which is
false for `%d`, so the call is refused at its precondition.

```c filename=fprintf_refuses_a_format_that_converts.c
#include <stdio.h>

int report(FILE *file, int value)
{
    return fprintf(file, "%d", value);
}
```

```click
verifying "fprintf_refuses_a_format_that_converts.c";
import click::c::stdio::{stream};

int32 report(FILE* file, int32 value) {
    owns out: stream(file);
    ensures true;
}
```

```expect
fail:unproved obligation: `click::c::stdio::literal_format(("fprintf_refuses_a_format_that_converts.c"::report.string_literal(0) as (uint8 *)), 0u64, 2) == true`
```
