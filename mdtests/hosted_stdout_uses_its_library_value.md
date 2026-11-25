# A standalone theorem and C execution share the linked stdout value

```c filename=stream.c
#include <stdio.h>
#ifndef stdout
#error stdout must be a macro
#endif

FILE *standard_stream(void)
{
    return stdout;
}
```

```click
verifying "stream.c";

theorem standard_stream_is_open() {
    ensures stdout != 0 by apply(stdout_non_null());
}

FILE* standard_stream() {
    ensures result == stdout;
}
```

```expect
pass
```
