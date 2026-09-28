# Consuming an acquisition requires releasing it

The visible resource clause does not permit a function to return while its
input acquisition still holds the lifetime loan.

```c filename=missing_release.c
#include <pthread.h>
struct holder { pthread_mutex_t mu; };
void release(struct holder *p) {}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "missing_release.c";
void release(struct holder *p) {
    owns access: mutex_use(&p->mu);
    consumes guard: mutex_guard(&p->mu);
} by {
    execute();
    simp();
}
```

```expect
fail: a function cannot return with a held mutex
```
