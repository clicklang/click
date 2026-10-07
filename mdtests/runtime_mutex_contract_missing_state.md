# Named initialization requires binding the lifetime output

An empty call map initializes an empty mutex without depositing the separately
owned state. The call still produces lifetime authority, which needs an output
binder.

```c filename=runtime_mutex_contract_missing_state.c
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

verifying "runtime_mutex_contract_missing_state.c";

void initialize(struct counter *counter) {
    owns &counter->mu;
    requires aligned(&counter->mu, 8);
    owns state: counter_state(counter);
} by {
    step(pthread_mutex_init(&counter->mu, 0), {});
}
```

```expect
fail: `pthread_mutex_init` produces named resource instance(s) `lifetime`
```
