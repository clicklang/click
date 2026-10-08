# A worker spends its member under authority it holds until join

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

```click resource_semantics=authority
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "modeled_pthread_counted_join.c";
authorized resource ticket(p: void*) {}
void* worker(void* argument) {
    owns authority(ticket(argument));
    consumes ticket(argument);
} by { unfold(ticket(argument)); execute(); simp(); }
int32 run(void* p) {
    owns authority(ticket(p));
    consumes ticket(p);
    requires count(ticket(p)) == 1;
    ensures result == 0 or result == 1;
} by {
    step();
    step();
    branch then { have count(ticket(p)) == 1; unfold(ticket(p)); step(); simp(); } else {}
    have old(count(ticket(p))) == 1;
    step();
    have count(ticket(p)) == 0;
    step();
    simp();
}
```

```expect
pass
```
