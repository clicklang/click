# Join commits a worker’s ordinary resource consumption

```c filename=modeled_pthread_counted_join.c
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
verifying "modeled_pthread_counted_join.c";
abstract resource ticket(p: void*);
void* worker(void* argument) {
    consumes ticket(argument);
} by { execute(); simp(); }
int32 run(void* p) {
    consumes ticket(p);
    requires count(ticket(p)) == 1;
    ensures result == 0 or result == 1;
} by {
    step();
    step();
    branch then { have count(ticket(p)) == 1 by { simp(); } step(); simp(); } else {}
    have old(count(ticket(p))) == 1 by { simp(); }
    step();
    have count(ticket(p)) == 0 by { simp(); }
    step();
    simp();
}
```

```expect
pass
```
