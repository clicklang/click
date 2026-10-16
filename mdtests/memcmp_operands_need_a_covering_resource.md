# memcmp reads each operand only under a covering resource

The standard-library `memcmp` contract `views` both operands, as every
external load needs a covering viewed or owned memory resource. Here the
caller views `b` but states only `viewable(a[0..4])` for `a`, which grants no
read authority, so the call is refused during planning for `a`. The same
function viewing both operands verifies
([`memcmp_const_unsigned_char_arguments.md`](memcmp_const_unsigned_char_arguments.md)).

```c filename=memcmp_operands_need_a_covering_resource.c
#include <string.h>
int compare4(const unsigned char *a, const unsigned char *b) {
    return memcmp(a, b, 4);
}
```

```click
verifying "memcmp_operands_need_a_covering_resource.c";
int32 compare4(const uint8* a, const uint8* b) {
    requires viewable(a[0..4]);
    views b[0..4];
    ensures result == 0 implies click::bytes::equal(a, 0u64, b, 0u64, 4u64);
} by {
    have forall (k: uint64) {
        k < 4u64 implies defined(a[k]) and defined(b[k])
    } by simp;
    execute();
    simp();
}
```

```expect
fail: the required loan backing or binding is missing refused during planning; selected resource `views a[0..4]`
```
