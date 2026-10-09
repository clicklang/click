# A worker spending a possibly aliased member needs that member's authority

Two workers each spend one `ticket(argument)`, started with `p` and `q`, and
nothing is known about `p` and `q`. A count comes from the authority's
ledger, so an aliased total is never ambiguous. The worker that spends `ticket(q)` needs
`authority(ticket(q))`; `run` holds only `authority(ticket(p))`, so starting
it is refused.

```c filename=authority_modeled_pthread_alias_worker_requires_authority.c
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
verifying "authority_modeled_pthread_alias_worker_requires_authority.c";
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
    consumes ticket(p);
    consumes ticket(q);
    requires count(ticket(p)) == 2;
    ensures result == 0 or result == 1;
} by {
    execute();
    simp();
}
```

```expect
fail: Requires owns authority(ticket(...))
```
