# A `bool` cell's read is its byte tested against zero

A `bool` object is one byte. Storing a `Bool` writes its cast `b as uint8`,
1 or 0, and reading the cell gives back the `Bool` `byte != 0`, so a value
stored and read again is the same `Bool`. A read of a cell this function did
not write, such as a global at entry, is `byte != 0` of a byte the type's
own invariant keeps at 0 or 1, and returning it as an `int` is its cast,
whose range is 0 or 1.

```c filename=bool_cells.c
#include <stdbool.h>

bool flag;

bool round_trip(int x) {
    bool stored = x;
    bool copy = stored;
    if (copy) {
        return true;
    }
    return stored;
}

int read_flag(void) { return flag; }
```

```click
verifying "bool_cells.c";

Bool round_trip(int32 x) {
    ensures result implies x != 0;
    ensures x != 0 implies result;
}

int32 read_flag() {
    ensures result == 0 or result == 1;
}
```

```expect
pass
```
