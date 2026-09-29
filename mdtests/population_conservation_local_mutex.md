# Population conservation through a locally owned mutex

This is a sequential composition control. It checks that committing a declared
consumption before unlock restores the population invariant. It does not yet
transfer population units to concurrent workers.

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

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "local_conservation.c";
resource remaining(p: struct counter*) {
    owns p->value;
    fact count(remaining(p)) <= 3;
    fact p->value == 3 - count(remaining(p));
}
resource counter_state(p: struct counter*) {
    field retained: int32;
    guarded_by p->mutex;
    owns retained of remaining(p);
    fact retained > 0;
}
void contribute(struct counter* p) {
    owns state: counter_state(p);
    consumes remaining(p);
    requires count(remaining(p)) > 1;
    requires state.retained > 0;
    requires count(remaining(p)) == state.retained + 1;
    owns &p->mutex;
    requires aligned(&p->mutex, 8);
    ensures state.retained == old(state.retained);
} by {
    let { lifetime: lifetime } = step(pthread_mutex_init(&p->mutex, 0), { state: state });
    step();
    let { retained: kept } = unfold(state);
    open(remaining(p)) {
        have count(remaining(p)) - 1 == kept by {
            simp();
        }
        have count(remaining(p)) - 1 >= 1 by {
            arithmetic() using { count(remaining(p)) > 1; count(remaining(p)) <= 3; }
        }
        have (3 - count(remaining(p))) + 1 == 3 - (count(remaining(p)) - 1) by {
            arithmetic() using { count(remaining(p)) > 1; count(remaining(p)) <= 3; }
        }
        have count(remaining(p)) - 1 <= 3 by {
            arithmetic() using { count(remaining(p)) > 1; count(remaining(p)) <= 3; }
        }
        step();
    }
    fold(state);
    step();
    step(pthread_mutex_destroy(&p->mutex), { lifetime: lifetime });
    step();
    simp();
}
uint32 twice(struct counter* p) {
    owns &p->mutex;
    requires aligned(&p->mutex, 8);
    owns p->value;
    ensures result == 2;
} by {
    step();
    fold(3 of remaining(p));
    let state = fold(counter_state(p), { retained: 2 });
    step(contribute(p), { state: state });
    unfold(state);
    let next = fold(counter_state(p), { retained: 1 });
    step(contribute(p), { state: next });
    unfold(next);
    unfold(remaining(p));
    step();
    simp();
}
```

```expect
pass
```
