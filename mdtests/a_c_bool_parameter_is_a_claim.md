# A C `bool` parameter is a claim

A C `bool` parameter written alone is the claim `flag == true`, which is
the test `flag != 0` that `if (flag)` makes, so a contract states each
branch's result without comparing with zero.

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
    ensures early implies result == 7;
    ensures not early implies result == 9;
    ensures early == true implies result == 7;
    ensures early != true implies result == 9;
    ensures result == (if early { 7 } else { 9 });
} by {
    execute();
    simp();
}
```

```expect
pass
```
