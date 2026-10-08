# Initialization rejects a duplicate state binder

One declared input cannot be supplied twice in the same call map.

```c filename=runtime_mutex_contract_duplicate_state.c
#include <pthread.h>
struct counter { pthread_mutex_t mu; int value; };

void initialize(struct counter *counter) {
    pthread_mutex_init(&counter->mu, 0);
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

verifying "runtime_mutex_contract_duplicate_state.c";

void initialize(struct counter *counter) {
    owns counter->mu;
    requires aligned(&counter->mu, 8);
    owns state: counter_state(counter);
} by {
    step(pthread_mutex_init(&counter->mu, 0), { state: state, state: state });
}
```

```expect
fail: duplicate binder `state` in the call map
```

