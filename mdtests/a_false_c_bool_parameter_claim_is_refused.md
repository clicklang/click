# A false claim about a C `bool` parameter is refused

```c filename=pick.c
#include <stdbool.h>

int pick(bool early) {
    if (early) {
        return 7;
    }
    return 9;
}
```

```click
verifying "pick.c";

int32 pick(bool early) {
    ensures not early implies result == 7;
}
```

```expect
fail: `ensures not early == true implies result == 7` failed for `pick.ensures_0` path 1: unclosed goal
```
