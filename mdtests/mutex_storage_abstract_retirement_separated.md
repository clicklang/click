# Abstract guard contracts need lifecycle support before retiring allocations

This C0 fixture uses the allocator builtins directly; the unsupported
`stdlib.h` include is omitted. The modeled pthread declarations are retained.


The helper must prove its allocation is separate from the input mutex's
reserved storage. A guard alone does not justify freeing a possibly overlapping
allocation.

```c filename=mutex_storage_abstract_retirement_separated.c
#include <pthread.h>
struct holder { pthread_mutex_t mu; };
void release_other(struct holder *holder, int *data) {
    free(data);
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "mutex_storage_abstract_retirement_separated.c";
void release_other(struct holder *holder, int32 *data) {
    requires data != 0;
    requires separate(memory(data[0..1]), memory(holder->mu));
    owns mutex_guard(&holder->mu);
    consumes allocation(data, 4);
    consumes data[0..1];
} by {
    execute();
    simp();
}
```

```expect
pass
```
