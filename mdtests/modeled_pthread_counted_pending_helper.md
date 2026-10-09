# A helper cannot observe an outstanding worker’s Count

```c filename=modeled_pthread_counted_pending_helper.c
#include <pthread.h>
#include <stddef.h>
void *worker(void *argument) { return NULL; }
void observe(void *p) {}
int run(void *p) {
    pthread_t handle;
    if (pthread_create(&handle, NULL, worker, p) != 0) return 0;
    observe(p);
    (void)pthread_join(handle, NULL);
    return 1;
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "modeled_pthread_counted_pending_helper.c";
authorized resource ticket(p: void*) {}
void* worker(void* argument) {
    owns authority(ticket(argument));
    consumes ticket(argument);
} by { unfold(ticket(argument)); execute(); simp(); }
void observe(void* p) {
    owns authority(ticket(p));
    ensures 1 == 1;
    requires count(ticket(p)) == 1;
} by { execute(); simp(); }
int32 run(void* p) {
    owns authority(ticket(p));
    consumes ticket(p);
    requires count(ticket(p)) == 1;
    ensures result == 0 or result == 1;
} by {
    step();
    step();
    branch then { unfold(ticket(p)); step(); simp(); } else {}
    step();
    step();
    step();
    simp();
}
```

```expect
fail: Requires owns authority(ticket(...))
```
