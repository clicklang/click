# Initialization accepts a differently named local state

The contract binder is `state`; the caller's folded resource instance is named `initial`.

```c filename=runtime_mutex_contract_renamed_state.c
#include <pthread.h>
struct counter { pthread_mutex_t mu; int value; };

int read_counter(struct counter *counter) {
    int value;
    pthread_mutex_init(&counter->mu, 0);
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

verifying "runtime_mutex_contract_renamed_state.c";

int32 read_counter(struct counter *counter) {
    owns &counter->mu;
    requires aligned(&counter->mu, 8);
    owns initial: counter_state(counter);
    ensures result == initial.value;
} by {
    step();
    let { lifetime: mutex_lifetime } = step(pthread_mutex_init(&counter->mu, 0), { state: initial });
    step();
    unfold(initial);
    step();
    fold(initial);
    step();
    step();
    step();
    simp();
}
```

```expect
pass
```

