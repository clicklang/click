# A produces clause cannot invent an acquisition

```c filename=missing_acquire.c
#include <pthread.h>
struct holder { pthread_mutex_t mu; };
void acquire(struct holder *p) {}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "missing_acquire.c";
void acquire(struct holder *p) {
    owns access: mutex_use(&p->mu);
    produces guard: mutex_guard(&p->mu);
} by {
    execute();
    simp();
}
```

```expect
fail: missing resource fact `owns mutex_guard(&p->mu)`
```
