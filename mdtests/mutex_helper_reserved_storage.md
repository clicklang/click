# An ordinary helper cannot reinitialize a live mutex

```c filename=mutex_helper_reserved_storage.c
#include <pthread.h>
struct holder { pthread_mutex_t mu; };
void reset(struct holder *p) { pthread_mutex_init(&p->mu, 0); }
void run(struct holder *p) {
    pthread_mutex_init(&p->mu, 0);
    reset(p);
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "mutex_helper_reserved_storage.c";
void reset(struct holder* p) {
    consumes p->mu;
    requires aligned(&p->mu, 8);
} by { execute(); simp(); }
void run(struct holder* p) {
    owns p->mu;
    requires aligned(&p->mu, 8);
} by { execute(); simp(); }
```

```expect
fail: initialized mutex storage is reserved until pthread_mutex_destroy
```
