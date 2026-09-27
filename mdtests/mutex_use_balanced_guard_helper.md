# A balanced use helper can lend its current guard to a preserving helper

```c filename=mutex_use_balanced_guard_helper.c
#include <pthread.h>
struct holder { pthread_mutex_t mu; };
void keep_guard(struct holder *holder) {}
void helper(struct holder *holder) {
    pthread_mutex_lock(&holder->mu);
    keep_guard(holder);
    pthread_mutex_unlock(&holder->mu);
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "mutex_use_balanced_guard_helper.c";
void keep_guard(struct holder *holder) {
    owns mutex_guard(&holder->mu);
} by { execute(); simp(); }
void helper(struct holder *holder) {
    owns mutex_use(&holder->mu);
} by {
    step();
    step(keep_guard(holder), {});
    step();
    step();
    simp();
}
```

```expect
pass
```
