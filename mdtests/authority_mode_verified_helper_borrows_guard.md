# A verified helper may borrow a held guard in authority mode

The helper borrows the guard and an ordinary resource and returns both
unchanged. Its body is checked under the same rules, and without a
`mutex_use` share it cannot reacquire a deposited control, so the call
changes no population.

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

resource counter_state(counter: struct counter*) {
    field value: int32;
    owns counter->value;
    fact counter->value == value;
}

verifying "guarded_resource_mutex_flow.c";

int32 read_locked(struct counter *counter) {
    owns mutex_guard(&counter->mu);
    owns state: counter_state(counter);
    ensures result == state.value;
} by {
    have held(&counter->mu);
    unfold(state);
    execute();
    fold(state);
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
    step(read_locked(counter), { state: state });
    step();
    step();
    step();
    simp();
}
```

```expect
pass
```
