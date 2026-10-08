# Population conservation through a locally owned mutex

This is a sequential composition control. It checks that committing a declared
consumption before unlock restores the population invariant. Under authority
semantics the mutex holds an ordinary control that owns the counter and the
population authority; spending one unit and incrementing the counter inside
the critical section restores its equation. It does not yet transfer
population units to concurrent workers.

```c filename=local_conservation.c
#include <pthread.h>
#include <stddef.h>
struct counter { pthread_mutex_t mutex; unsigned int value; };
void contribute(struct counter *p) {
    pthread_mutex_init(&p->mutex, NULL);
    (void)pthread_mutex_lock(&p->mutex);
    p->value = p->value + 1u;
    (void)pthread_mutex_unlock(&p->mutex);
    (void)pthread_mutex_destroy(&p->mutex);
}
unsigned int twice(struct counter *p) {
    p->value = 0u;
    contribute(p);
    contribute(p);
    return p->value;
}
```

```click resource_semantics=authority
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "local_conservation.c";
authorized resource remaining(p: struct counter*) {}
resource control(p: struct counter*) {
    field value: uint32;
    owns p->value;
    owns authority(remaining(p));
    fact p->value == value;
    fact count(remaining(p)) <= 3;
    fact p->value == 3 - count(remaining(p));
}
void contribute(struct counter* p) {
    owns authority(remaining(p));
    owns p->value;
    consumes remaining(p);
    requires count(remaining(p)) > 1;
    requires count(remaining(p)) <= 3;
    requires p->value == 3 - count(remaining(p));
    owns p->mutex;
    requires aligned(&p->mutex, 8);
    ensures p->value == 3 - count(remaining(p));
} by {
    let state = fold(control(p), { value: p->value });
    let { lifetime: lifetime } = step(pthread_mutex_init(&p->mutex, 0), { state: state });
    step();
    unfold(state);
    have (3 - count(remaining(p))) + 1 == 3 - (count(remaining(p)) - 1) by {
        arithmetic() using { count(remaining(p)) > 1; count(remaining(p)) <= 3; }
    }
    unfold(remaining(p));
    step();
    let state = fold(control(p), { value: p->value });
    step();
    step(pthread_mutex_destroy(&p->mutex), { lifetime: lifetime });
    unfold(state);
    step();
    simp();
}
uint32 twice(struct counter* p) {
    owns authority(remaining(p));
    requires count(remaining(p)) == 0;
    owns p->mutex;
    requires aligned(&p->mutex, 8);
    owns p->value;
    ensures result == 2;
} by {
    step();
    fold(3 of remaining(p));
    step();
    step();
    unfold(remaining(p));
    step();
    simp();
}
```

```expect
pass
```
