# An `allocates` result is no pointer the caller held

`allocates(result, n)` is `produces allocation(result, n)` of an allocation
the call creates: a block no pointer that existed before the call reaches,
as none reaches `malloc`'s. So the returned pointer differs from any pointer
the caller already held, even one whose memory it does not own.

```c filename=an_allocates_result_is_no_pointer_the_caller_held.c
#include <stdlib.h>

int *fresh_int(void);

int differs(int *held) {
    int *p = fresh_int();
    int different = p != held;
    free(p);
    return different;
}
```

```click
verifying "an_allocates_result_is_no_pointer_the_caller_held.c";

extern int32* fresh_int() {
    allocates(result, 4);
    produces *result;
    ensures result != 0;
}

int32 differs(int32* held) {
    ensures result == 1;
}
```

```expect
pass
```
