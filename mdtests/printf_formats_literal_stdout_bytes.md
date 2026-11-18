# A literal printf records its exact bytes and result

The adjacent format tokens form one C string. The escaped percent writes
one byte and formatting stops at the first NUL.

```c filename=output.c
#include <stdio.h>
int output(void) {
    return printf("a" "%%\0ignored");
}
```

```click
verifying "output.c";
import click::c::stdio;

int32 output() {
    owns out: stdio::stdout();
    ensures out.writes == List::Cons(
        StdoutWrite::Attempt(List::Cons('a', List::Cons('%', List<uint8>::Nil)), result),
        old(out.writes));
    ensures result == 2 or result < 0;
}
```

```expect
pass
```
