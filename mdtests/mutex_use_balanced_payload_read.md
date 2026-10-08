# Use authority grants no access to protected payload

```c filename=mutex_use_balanced_payload_read.c
#include <pthread.h>
struct holder { pthread_mutex_t mu; int value; };
int helper(struct holder *holder) {
    int value;
    pthread_mutex_lock(&holder->mu);
    value = holder->value;
    pthread_mutex_unlock(&holder->mu);
    return value;
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "mutex_use_balanced_payload_read.c";

int32 helper(struct holder *holder) {
    owns mutex_use(&holder->mu);
} by {
    execute();
    simp();
}
```

```expect
fail: missing resource fact `views holder->value`
```
