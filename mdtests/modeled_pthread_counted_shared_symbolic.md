# Borrowing workers over an opaque total of at least two

```c filename=modeled_pthread_counted_shared_symbolic.c
#include <pthread.h>
#include <stddef.h>
void *worker(void *argument) { return NULL; }
int run(void *p, void *q, int n) {
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

```click
target "x86_64-unknown-linux-gnu";
runtime "modeled-pthread";
verifying "modeled_pthread_counted_shared_symbolic.c";
authorized resource ticket(p: void*) {}
void* worker(void* argument) {
    owns ticket(argument);
} by { execute(); simp(); }
int32 run(void* p, void* q, int32 n) {
    owns authority(ticket(p));
    owns authority(ticket(q));
    consumes 2 of ticket(p);
    owns ticket(q);
    requires p != q;
    requires n >= 2;
    requires to_integer(count(ticket(p))) == to_integer(n);
    requires to_integer(count(ticket(q))) == 1;
    ensures result == 0 or result == 1;
} by {
    step();
    step();
    step();
    branch {
        have to_integer(count(ticket(p))) == to_integer(n);
        unfold(ticket(p));
        unfold(ticket(p));
        step(); simp();
    } else {}
    step();
    branch {
        step();
        unfold(ticket(p));
        unfold(ticket(p));
        have to_integer(count(ticket(q))) == 1;
        step(); simp();
    } else {}
    step();
    unfold(ticket(p));
    have to_integer(count(ticket(p))) == to_integer(n - 1);
    step();
    unfold(ticket(p));
    have to_integer(count(ticket(p))) == to_integer(n - 2);
    have to_integer(count(ticket(q))) == 1;
    step(); simp();
}
```

```expect
pass
```
