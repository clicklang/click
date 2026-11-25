# A failed claim names stdout by its declaration

```c filename=stream.c
#include <stdio.h>

FILE *standard_stream(void)
{
    return stdout;
}
```

```click
verifying "stream.c";

FILE* standard_stream() {
    ensures result == 0;
}
```

```expect
fail: left side evaluated to stdout
```
