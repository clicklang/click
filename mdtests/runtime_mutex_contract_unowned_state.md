# Initialization cannot publish a named state hidden in a wrapper

`state` is a declared caller instance, but folding `package` moves its
ownership into the wrapper. The call map still resolves the name, and the
runtime transition must reject publication without folded ownership of that
specific instance.

```c filename=runtime_mutex_contract_unowned_state.c
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

resource package(counter: struct counter*) {
    field tag: int32;
    owns child: counter_state(counter);
    fact child.value == tag;
}

verifying "runtime_mutex_contract_unowned_state.c";

void initialize(struct counter *counter) {
    owns &counter->mu;
    requires aligned(&counter->mu, 8);
    owns state: counter_state(counter);
} by {
    let wrapped = fold(package(counter), { tag: state.value }, { child: state });
    let { lifetime: mutex_lifetime } = step(pthread_mutex_init(&counter->mu, 0), { state: state });
}
```

```expect
fail: selected mutex invariant is not held folded
```
