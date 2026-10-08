# A runtime-produced lifecycle name crosses an ordinary helper contract

The folded counter resource moves into a modeled mutex at initialization.
Locking retrieves it so the C body can read the counter. Unlocking requires
that resource folded again, and destroying the mutex returns it to the caller.

```c filename=mutex_lifetime_named_runtime.c
#include <pthread.h>
struct counter { pthread_mutex_t mu; int value; };

void keep(struct counter *counter) {}

int read_counter(struct counter *counter) {
    int value;
    pthread_mutex_init(&counter->mu, 0);
    keep(counter);
    pthread_mutex_lock(&counter->mu);
    value = counter->value;
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

verifying "mutex_lifetime_named_runtime.c";

void keep(struct counter *counter) {
    owns lifetime: mutex_live(&counter->mu);
} by { execute(); simp(); }

int32 read_counter(struct counter *counter) {
    owns counter->mu;
    requires aligned(&counter->mu, 8);
    owns state: counter_state(counter);
    ensures result == state.value;
} by {
    step();
    let { lifetime: mutex_lifetime } = step(pthread_mutex_init(&counter->mu, 0), { state: state });
    step(keep(counter), { lifetime: mutex_lifetime });
    step();
    unfold(state);
    step();
    fold(state);
    step();
    step(pthread_mutex_destroy(&counter->mu), { lifetime: mutex_lifetime });
    step();
    simp();
}
```

```expect
pass
```
