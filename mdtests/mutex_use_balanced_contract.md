# A use helper acquires and releases an empty mutex

The nested helper returns the same use permission after a balanced local
acquisition. No protected payload resource is supplied.

```c filename=mutex_use_balanced_contract.c
#include <pthread.h>
struct holder { pthread_mutex_t mu; };
void inner(struct holder *holder) {
    pthread_mutex_lock(&holder->mu);
    pthread_mutex_unlock(&holder->mu);
}
void outer(struct holder *holder) { inner(holder); }
int run(struct holder *holder) {
    pthread_mutex_init(&holder->mu, 0);
    outer(holder);
    pthread_mutex_destroy(&holder->mu);
    return 0;
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "mutex_use_balanced_contract.c";

void inner(struct holder *holder) {
    owns mutex_use(&holder->mu);
} by {
    step();
    step();
    step();
    simp();
}
void outer(struct holder *holder) {
    owns mutex_use(&holder->mu);
} by {
    step(inner(holder), {});
    step();
    simp();
}
int32 run(struct holder *holder) {
    owns holder->mu;
    requires aligned(&holder->mu, 8);
    ensures result == 0;
} by {
    step();
    step(outer(holder), {});
    step();
    step();
    simp();
}
```

```expect
pass
```
