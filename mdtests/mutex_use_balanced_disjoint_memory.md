# Balanced use helpers preserve disjoint owned payload

```c filename=mutex_use_balanced_disjoint_memory.c
#include <pthread.h>
struct holder { pthread_mutex_t mu; int value; };
void helper(struct holder *holder) {
    pthread_mutex_lock(&holder->mu);
    pthread_mutex_unlock(&holder->mu);
}
int run(struct holder *holder) {
    pthread_mutex_init(&holder->mu, 0);
    helper(holder);
    pthread_mutex_destroy(&holder->mu);
    return holder->value;
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "mutex_use_balanced_disjoint_memory.c";
void helper(struct holder *holder) {
    owns mutex_use(&holder->mu);
} by { execute(); simp(); }
int32 run(struct holder *holder) {
    owns holder->mu;
    owns holder->value;
    requires aligned(&holder->mu, 8);
    ensures result == old(holder->value);
} by {
    step();
    step(helper(holder), {});
    step();
    step();
    simp();
}
```

```expect
pass
```
