# Workers consume one shared abstract population in either join order

```c filename=modeled_pthread_counted_shared_observer.c
#include <pthread.h>
#include <stddef.h>
void *worker(void *argument) { return NULL; }
void *consumer(void *argument) { return NULL; }
int run(void *p, void *q) {
    pthread_t first;
    pthread_t second;
    if (pthread_create(&first, NULL, worker, p) != 0) return 0;
    if (pthread_create(&second, NULL, consumer, p) != 0) {
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
verifying "modeled_pthread_counted_shared_observer.c";
abstract resource ticket(p: void*);
void* worker(void* argument) {
    owns ticket(argument);
    ensures count(ticket(argument)) >= 1;
} by { execute(); simp(); }
void* consumer(void* argument) {
    consumes ticket(argument);
} by { execute(); simp(); }
int32 run(void* p, void* q) {
    consumes 2 of ticket(p);
    consumes ticket(q);
    requires p != q;
    requires count(ticket(p)) == 2;
    requires count(ticket(q)) == 1;
    ensures result == 0 or result == 1;
} by {
    step();
    step();
    step();
    branch then { have count(ticket(p)) == 2 by { simp(); } step(); simp(); } else {}
    step();
    branch then {
        step();
        have count(ticket(p)) == 1 by { simp(); }
        have count(ticket(q)) == 1 by { simp(); }
        step(); simp();
    } else {}
    step();
    have count(ticket(q)) == 1 by { simp(); }
    step();
    have count(ticket(p)) == 0 by { simp(); }
    have count(ticket(q)) == 1 by { simp(); }
    step(); simp();
}
```

```expect
fail: Requires joining the worker using ticket(...) before another population transfer
```
