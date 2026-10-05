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
abstract resource ticket(p: void*);
void* worker(void* argument) {
    consumes ticket(argument);
} by { execute(); simp(); }
void observe(void* p) {
    ensures 1 == 1;
    requires count(ticket(p)) == 1;
} by { execute(); simp(); }
int32 run(void* p) {
    consumes ticket(p);
    requires count(ticket(p)) == 1;
    ensures result == 0 or result == 1;
} by {
    step();
    step();
    branch then { step(); simp(); } else {}
    step();
    step();
    step();
    simp();
}
```

```expect
fail: count(...) requires joining its outstanding worker
```
