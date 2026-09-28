# Direct pthread typedef parameters remain an explicit surface limitation

This frozen C example exercises empty mutex helpers. The current sidecar
parser cannot yet name `pthread_mutex_t` as a parameter type. Keep that
limitation explicit rather than rewriting the C into a containing struct.

```c filename=mutex_helper_transfers_empty.c
#include <pthread.h>
void acquire(pthread_mutex_t *mu) { pthread_mutex_lock(mu); }
void release(pthread_mutex_t *mu) { pthread_mutex_unlock(mu); }
void use(pthread_mutex_t *mu) { acquire(mu); release(mu); }
void run(pthread_mutex_t *mu) {
    pthread_mutex_init(mu, 0);
    acquire(mu);
    release(mu);
    use(mu);
    pthread_mutex_destroy(mu);
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "mutex_helper_transfers_empty.c";

void acquire(pthread_mutex_t *mu) {
    owns access: mutex_use(mu);
    produces guard: mutex_guard(mu);
} by {
    let { guard: acquired } = step(pthread_mutex_lock(mu), { access: access });
    step();
    simp();
}
void release(pthread_mutex_t *mu) {
    owns access: mutex_use(mu);
    consumes guard: mutex_guard(mu);
} by {
    step(pthread_mutex_unlock(mu), { access: access, guard: guard });
    step();
    simp();
}
void use(pthread_mutex_t *mu) {
    owns permission: mutex_use(mu);
} by {
    let { guard: acquired } = step(acquire(mu), { access: permission });
    step(release(mu), { access: permission, guard: acquired });
    step();
    simp();
}
void run(pthread_mutex_t *mu) {
    owns mu;
    requires aligned(mu, 8);
} by {
    let { lifetime: lifetime } = step(pthread_mutex_init(mu, 0));
    let { guard: acquired } = step(acquire(mu), { access: lifetime });
    step(release(mu), { access: lifetime, guard: acquired });
    step(use(mu), { permission: lifetime });
    step(pthread_mutex_destroy(mu), { lifetime: lifetime });
    step();
    simp();
}
```

```expect
fail: unknown C type `pthread_mutex_t`
```
