# Workers spending possibly aliased populations do not certify a count

Two workers each consume one `ticket(argument)`, started with `p` and `q`. The
caller states nothing about `p` and `q`, so `count(ticket(p))` has no value
the facts determine: with `p == q` both workers spend units of one population.
The observation is refused rather than certifying `count(ticket(p)) == 1`
after both joins. `modeled_pthread_counted_shared_join.md` is the passing
form with `requires p != q`.

```c filename=modeled_pthread_population_count_alias_rejected.c
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
verifying "modeled_pthread_population_count_alias_rejected.c";
abstract resource ticket(p: void*);
void* worker(void* argument) {
    consumes ticket(argument);
} by { execute(); simp(); }
int32 run(void* p, void* q) {
    consumes ticket(p);
    consumes ticket(q);
    requires count(ticket(p)) == 2;
    ensures result == 0 or result == 1;
    ensures result == 1 implies count(ticket(p)) == 1;
} by {
    execute();
    simp();
}
```

```expect
fail: may alias
```
