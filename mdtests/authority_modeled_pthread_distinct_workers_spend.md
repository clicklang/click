# Workers spend members of two distinct populations under their authorities

`run` holds the authorities for `ticket(p)` and `ticket(q)`, which are
distinct, and lends one to each worker to spend one member. This is the
passing companion of `authority_modeled_pthread_alias_worker_requires_authority.md`.

```c filename=authority_modeled_pthread_distinct_workers_spend.c
#include <pthread.h>
#include <stddef.h>
void *worker(void *argument) { return NULL; }
int run(void *p, void *q) {
    pthread_t first;
    pthread_t second;
    if (pthread_create(&first, NULL, worker, p) != 0) return 0;
    if (pthread_create(&second, NULL, worker, q) != 0) {
        (void)pthread_join(first, NULL);
        return 0;
    }
    (void)pthread_join(second, NULL);
    (void)pthread_join(first, NULL);
    return 1;
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "authority_modeled_pthread_distinct_workers_spend.c";
authorized resource ticket(p: void*) {}
void* worker(void* argument) {
    owns authority(ticket(argument));
    consumes ticket(argument);
} by {
    unfold(ticket(argument));
    execute();
    simp();
}
int32 run(void* p, void* q) {
    owns authority(ticket(p));
    owns authority(ticket(q));
    consumes ticket(p);
    consumes ticket(q);
    requires p != q;
    requires count(ticket(p)) == 2;
    ensures result == 0 or result == 1;
} by {
    execute();
    simp();
}
```

```expect
pass
```
