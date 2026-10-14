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
} by {
    execute();
    simp();
}
```

```expect
fail: did not retain a complete proof for `pick.ensures_0`
```
