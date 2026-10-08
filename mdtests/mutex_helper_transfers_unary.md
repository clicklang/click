# Empty mutex helpers preserve their lifetime dependency

```c filename=mutex_helper_transfers_unary.c
#include <pthread.h>
struct holder { pthread_mutex_t mu; };
void acquire(struct holder *p) { pthread_mutex_lock(&p->mu); }
void release(struct holder *p) { pthread_mutex_unlock(&p->mu); }
void use(struct holder *p) { acquire(p); release(p); }
void run(struct holder *p) {
    pthread_mutex_init(&p->mu, 0);
    acquire(p);
    release(p);
    use(p);
    pthread_mutex_destroy(&p->mu);
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "mutex_helper_transfers_unary.c";

void acquire(struct holder *p) {
    owns access: mutex_use(&p->mu);
    produces guard: mutex_guard(&p->mu);
} by {
    step();
    step();
    simp();
}
void release(struct holder *p) {
    owns access: mutex_use(&p->mu);
    consumes guard: mutex_guard(&p->mu);
} by {
    step();
    step();
    simp();
}
void use(struct holder *p) {
    owns permission: mutex_use(&p->mu);
} by {
    let { guard: acquired } = step(acquire(p), { access: permission });
    step(release(p), { access: permission, guard: acquired });
    step();
    simp();
}
void run(struct holder *p) {
    owns p->mu;
    requires aligned(&p->mu, 8);
} by {
    let { lifetime: lifetime } = step(pthread_mutex_init(&p->mu, 0), {});
    let { guard: acquired } = step(acquire(p), { access: lifetime });
    step(release(p), { access: lifetime, guard: acquired });
    step(use(p), { permission: lifetime });
    step(pthread_mutex_destroy(&p->mu), { lifetime: lifetime });
    step();
    simp();
}
```

```expect
pass
```
