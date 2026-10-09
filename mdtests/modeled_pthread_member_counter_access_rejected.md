# A worker that borrows only a member cannot read the counter

The creator keeps the authority-bearing control that owns the counter and lends
one member to a worker. The member grants no memory, so the worker's read of the
counter is refused.

```c filename=modeled_pthread_member_counter_access_rejected.c
#include <pthread.h>
#include <stddef.h>

struct cell { int refs; };

void *worker(void *argument) {
    struct cell *cell = argument;
    int seen = cell->refs;
    return NULL;
}

int run(struct cell *cell) {
    pthread_t handle;
    if (pthread_create(&handle, NULL, worker, cell) != 0) return 0;
    (void)pthread_join(handle, NULL);
    return 1;
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
authorized resource reference(cell: struct cell*) {}
verifying "modeled_pthread_member_counter_access_rejected.c";

void *worker(void *argument) {
    owns reference((struct cell *)argument);
} by {
    execute();
    simp();
}

int32 run(struct cell *cell) {
    owns authority(reference(cell));
    owns reference(cell);
    owns cell->refs;
    ensures result == 0 or result == 1;
} by {
    execute();
    simp();
}
```

```expect
fail: views
```
