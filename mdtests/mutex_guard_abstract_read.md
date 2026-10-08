# A helper reads protected memory through an abstract guard

A preserving contract frames the wrapper and its acquisition. The helper
receives no permission to change the mutex protocol.

```c filename=guarded_resource_mutex_flow.c
#include <pthread.h>
struct counter { pthread_mutex_t mu; int value; };

int read_locked(struct counter *counter) { return counter->value; }

int read_counter(struct counter *counter) {
    int value;
    pthread_mutex_init(&counter->mu, 0);
    pthread_mutex_lock(&counter->mu);
    value = read_locked(counter);
    pthread_mutex_unlock(&counter->mu);
    pthread_mutex_destroy(&counter->mu);
    return value;
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";

resource holding(counter: struct counter*) {
    field tag: int32;
    owns mutex_guard(&counter->mu);
}

resource counter_state(counter: struct counter*) {
    field value: int32;
    owns counter->value;
    fact counter->value == value;
}

verifying "guarded_resource_mutex_flow.c";

int32 read_locked(struct counter *counter) {
    owns h: holding(counter);
    owns state: counter_state(counter);
    ensures result == state.value;
} by {
    unfold(h);
    have held(&counter->mu);
    unfold(state);
    execute();
    fold(state);
    fold(h);
    simp();
}

int32 read_counter(struct counter *counter) {
    owns counter->mu;
    requires aligned(&counter->mu, 8);
    owns state: counter_state(counter);
    ensures result == state.value;
} by {
    step();
    let { lifetime: mutex_lifetime } = step(pthread_mutex_init(&counter->mu, 0), { state: state });
    step();
    let held = fold(holding(counter), { tag: 0 });
    step(read_locked(counter), { h: held, state: state });
    unfold(held);
    step();
    step();
    step();
    simp();
}
```

```expect
pass
```
