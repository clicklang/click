# A produced allocation may be a pointer the caller held

`produces allocation(result, n)` hands the caller an allocation without
saying it is new: an arena's `take(p)` returns the very pointer it was
given. So the returned pointer may equal one the caller held without owning
its memory, and a claim that it differs is refused. The same claim holds
for `allocates(result, n)`
(`mdtests/an_allocates_result_is_no_pointer_the_caller_held.md`).

```c filename=a_produced_allocation_may_be_a_pointer_the_caller_held.c
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
verifying "a_produced_allocation_may_be_a_pointer_the_caller_held.c";

extern int32* fresh_int() {
    produces allocation(result, 4);
    produces *result;
    ensures result != 0;
}

int32 differs(int32* held) {
    ensures result == 1;
}
```

```expect
fail: `ensures result == 1` failed for `differs.ensures_0`
```
