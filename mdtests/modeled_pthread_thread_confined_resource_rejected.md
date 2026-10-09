# A member lent to a worker exposes no shared accounting

A member is not thread confined: lending it to a worker is an ordinary transfer. The protected property is that a member alone
cannot expose the population's accounting. The creator keeps the authority and
the counter; the worker borrows only one member, so its claim about the count
is refused because it lacks the authority.

```c filename=modeled_pthread_thread_confined_resource_rejected.c
#include <pthread.h>
#include <stddef.h>

struct cell { int refs; };

void *worker(void *argument) {
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
verifying "modeled_pthread_thread_confined_resource_rejected.c";

void *worker(void *argument) {
    owns reference((struct cell *)argument);
    ensures count(reference((struct cell *)argument)) >= 1;
} by {
    execute();
    simp();
}

int32 run(struct cell *cell) {
    owns authority(reference(cell));
    owns reference(cell);
    ensures result == 0 or result == 1;
} by {
    execute();
    simp();
}
```

```expect
fail: count(...) requires owning authority for that population
```
