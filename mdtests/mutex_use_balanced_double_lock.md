# A use helper cannot acquire a mutex it already holds

```c filename=mutex_use_balanced_double_lock.c
#include <pthread.h>
struct holder { pthread_mutex_t mu; };
void helper(struct holder *holder) {
    pthread_mutex_lock(&holder->mu);
    pthread_mutex_lock(&holder->mu);
    pthread_mutex_unlock(&holder->mu);
    pthread_mutex_unlock(&holder->mu);
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "mutex_use_balanced_double_lock.c";

void helper(struct holder *holder) {
    owns mutex_use(&holder->mu);
} by {
    execute();
    simp();
}
```

```expect
fail: Click cannot acquire or lend mutex_use while a possibly aliasing mutex_guard is held
```
