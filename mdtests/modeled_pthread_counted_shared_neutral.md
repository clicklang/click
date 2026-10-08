# Workers consume one shared abstract population in either join order

```c filename=modeled_pthread_counted_shared_neutral.c
#include <pthread.h>
#include <stddef.h>
void *worker(void *argument) { return NULL; }
int run(void *p, void *q) {
    pthread_t first;
    pthread_t second;
    if (pthread_create(&first, NULL, worker, p) != 0) return 0;
    if (pthread_create(&second, NULL, worker, p) != 0) {
        (void)pthread_join(first, NULL);
        return 0;
    }
    (void)pthread_join(second, NULL);
    (void)pthread_join(first, NULL);
    return 1;
}
```

```click resource_semantics=authority
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "modeled_pthread_counted_shared_neutral.c";
authorized resource ticket(p: void*) {}
void* worker(void* argument) {
    owns ticket(argument);
} by { execute(); simp(); }
int32 run(void* p, void* q) {
    owns authority(ticket(p));
    owns authority(ticket(q));
    owns 2 of ticket(p);
    owns ticket(q);
    requires p != q;
    requires count(ticket(p)) == 2;
    requires count(ticket(q)) == 1;
    ensures result == 0 or result == 1;
} by {
    step();
    step();
    step();
    branch then {
        have count(ticket(p)) == 2;
        step(); simp();
    } else {}
    step();
    branch then {
        step();
        have count(ticket(q)) == 1;
        step(); simp();
    } else {}
    step();
    have count(ticket(p)) == 2;
    step();
    have count(ticket(p)) == 2;
    have count(ticket(q)) == 1;
    step(); simp();
}
```

```expect
pass
```
