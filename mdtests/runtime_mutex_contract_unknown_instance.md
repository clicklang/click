# Initialization rejects an unknown local resource name

The named input must identify a caller resource instance. Here `state` is not in the caller contract.

```c filename=runtime_mutex_contract_unknown_instance.c
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

verifying "runtime_mutex_contract_unknown_instance.c";

void initialize(struct counter *counter) {
    owns counter->mu;
    requires aligned(&counter->mu, 8);
} by {
    step(pthread_mutex_init(&counter->mu, 0), { state: state });
}
```

```expect
fail: unknown resource instance `state`
```
