# A use call does not preserve observations of mutex representation bytes

```c filename=mutex_use_balanced_storage_observation.c
#include <pthread.h>
struct holder { pthread_mutex_t mu; };
void helper(struct holder *holder) {
    pthread_mutex_lock(&holder->mu);
    pthread_mutex_unlock(&holder->mu);
}
int run(struct holder *holder) {
    pthread_mutex_init(&holder->mu, 0);
    unsigned char *bytes = (unsigned char *)&holder->mu;
    int before = bytes[0];
    helper(holder);
    int after = bytes[0];
    pthread_mutex_destroy(&holder->mu);
    return before == after;
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "mutex_use_balanced_storage_observation.c";
void helper(struct holder *holder) {
    owns mutex_use(&holder->mu);
} by { execute(); simp(); }
int32 run(struct holder *holder) {
    owns holder->mu;
    requires aligned(&holder->mu, 8);
    ensures result == 1;
} by {
    step();
    step();
    step();
    step();
    step();
    step(helper(holder), {});
    step();
    step();
    step();
    step();
    simp();
}
```

```expect
fail: ensures result == 1
```
