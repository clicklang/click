# `printf` refuses a format that converts an argument

`printf` has the `fprintf` contract with the stream `stdout`. Click models
a format of ordinary characters and `%%`; its contract requires
`click::c::stdio::literal_format` of the format, which is false for `%d`,
so the call is refused at its precondition.

```c filename=printf_refuses_a_format_that_converts.c
#include <stdio.h>

int report(int value)
{
    return printf("%d", value);
}
```

```click
verifying "printf_refuses_a_format_that_converts.c";
import click::c::stdio::{stream};

int32 report(int32 value) {
    owns out: stream(stdout);
    ensures true;
}
```

```expect
fail:unproved obligation: `click::c::stdio::literal_format(
```
