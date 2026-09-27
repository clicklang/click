# A wrapper cannot hide an acquisition from a use helper

```c filename=mutex_use_balanced_hidden_guard.c
#include <pthread.h>
struct holder { pthread_mutex_t mu; };
void helper(struct holder *holder) {
    pthread_mutex_lock(&holder->mu);
    pthread_mutex_unlock(&holder->mu);
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";

resource holding(holder: struct holder*) {
    field tag: int32;
    owns mutex_guard(&holder->mu);
}

verifying "mutex_use_balanced_hidden_guard.c";

void helper(struct holder *holder) {
    owns mutex_use(&holder->mu);
    owns h: holding(holder);
} by {
    execute();
    simp();
}
```

```expect
fail: Click cannot acquire or lend mutex_use while a possibly aliasing mutex_guard is held
```
