# Independent populations can join in reverse order

```c filename=modeled_pthread_counted_reverse_join.c
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

```click resource_semantics=authority
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "modeled_pthread_counted_reverse_join.c";
resource ticket(p: void*) {}
void* worker(void* argument) {
    owns authority(ticket(argument));
    consumes ticket(argument);
} by { unfold(ticket(argument)); execute(); simp(); }
int32 run(void* p, void* q) {
    owns authority(ticket(p));
    owns authority(ticket(q));
    consumes ticket(p);
    consumes ticket(q);
    requires p != q;
    requires count(ticket(p)) == 1;
    requires count(ticket(q)) == 1;
    ensures result == 0 or result == 1;
} by {
    step();
    step();
    step();
    branch then {
        have count(ticket(p)) == 1 by { simp(); }
        unfold(ticket(p));
        unfold(ticket(q));
        step(); simp();
    } else {}
    step();
    branch then {
        step();
        have count(ticket(p)) == 0 by { simp(); }
        have count(ticket(q)) == 1 by { simp(); }
        unfold(ticket(q));
        step(); simp();
    } else {}
    step();
    have count(ticket(q)) == 0 by { simp(); }
    step();
    have count(ticket(p)) == 0 by { simp(); }
    have count(ticket(q)) == 0 by { simp(); }
    step(); simp();
}
```

```expect
pass
```
