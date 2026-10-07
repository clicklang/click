# Unlock cannot restore a population after two increments

The contract permits consuming one unit. Increasing the value by two cannot
restore the control's conservation equation, so the control cannot be folded
again for unlock.

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

```click resource_semantics=authority
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "local_conservation.c";
resource remaining(p: struct counter*) {}
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
    owns &p->mutex;
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
```

```expect
fail: fold requires the instance body facts for the proposed fields: fact 3 of 3 of the resource body is not established
```
