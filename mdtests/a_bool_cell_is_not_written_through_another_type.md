# A `bool` cell is not written through another type

A `bool` object's byte is 1 or 0: every store of a `Bool` writes its cast
`b as uint8`. A write through a pointer of another type could leave any byte
there, so such a pointer to a `bool` object is refused rather than read
back as `byte != 0`.

```c filename=bool_byte_write.c
#include <stdbool.h>

bool overwrite(void) {
    bool b = true;
    unsigned char *p = (unsigned char *)&b;
    *p = 2;
    return b;
}
```

```click
verifying "bool_byte_write.c";

Bool overwrite() {
    ensures result;
}
```

```expect
fail: `step()` could not verify C operation: type mismatch
```
