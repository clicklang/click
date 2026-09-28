# Unlock cannot restore a population after two increments

The contract permits consuming one unit. Increasing the value by two cannot
restore the shared invariant before unlock.

```c filename=local_conservation.c
#include <pthread.h>
#include <stddef.h>
struct counter { pthread_mutex_t mutex; unsigned int value; };
void contribute(struct counter *p) {
    pthread_mutex_init(&p->mutex, NULL);
    (void)pthread_mutex_lock(&p->mutex);
    p->value = p->value + 2u;
    (void)pthread_mutex_unlock(&p->mutex);
    (void)pthread_mutex_destroy(&p->mutex);
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
    field marker: int32;
    guarded_by p->mutex;
    owns remaining(p);
    fact marker == 0;
}
void contribute(struct counter* p) {
    owns state: counter_state(p);
    consumes remaining(p);
    requires count(remaining(p)) > 1;
    owns &p->mutex;
    requires aligned(&p->mutex, 8);
} by {
    let { lifetime: lifetime } = step(pthread_mutex_init(&p->mutex, 0), { state: state });
    step();
    unfold(state);
    open(remaining(p)) {
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
```

```expect
fail: Requires p->value == (3 - count(remaining(p))) after consumption
```
