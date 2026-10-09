# A worker that borrows only a member leaves the count observable

The worker borrows one member and no authority, so it cannot change the total.
The parent keeps the authority and observes the exact count before join.

```c filename=modeled_pthread_counted_neutral_observed.c
#include <pthread.h>
#include <stddef.h>
void *worker(void *argument) { return NULL; }
int run(void *p) {
    pthread_t handle;
    if (pthread_create(&handle, NULL, worker, p) != 0) return 0;
    (void)pthread_join(handle, NULL);
    return 1;
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "modeled_pthread_counted_neutral_observed.c";
authorized resource ticket(p: void*) {}
void* worker(void* argument) {
    owns ticket(argument);
} by { execute(); simp(); }
int32 run(void* p) {
    owns authority(ticket(p));
    owns ticket(p);
    requires count(ticket(p)) == 1;
    ensures result == 0 or result == 1;
} by {
    step();
    step();
    branch then { step(); simp(); } else {}
    have count(ticket(p)) == 1;
    step();
    step();
    simp();
}
```

```expect
pass
```
