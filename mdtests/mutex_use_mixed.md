# Mutex use composes with memory ownership and stable views

```c filename=mutex_use_mixed.c
#include <pthread.h>
struct holder { pthread_mutex_t mu; };
void inner(struct holder *holder, int *out, int *value) { *out = *value; }
void outer(struct holder *holder, int *out, int *value) { inner(holder, out, value); }
int run(struct holder *holder, int *out, int *value) {
    pthread_mutex_init(&holder->mu, 0);
    outer(holder, out, value);
    outer(holder, out, value);
    pthread_mutex_destroy(&holder->mu);
    return *out;
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "mutex_use_mixed.c";
void inner(struct holder *holder, int32 *out, int32 *value) {
    owns mutex_use(&holder->mu);
    owns out[0..1];
    views value[0..1];
    requires separate(memory(out[0..1]), memory(holder->mu));
    ensures *out == *value;
} by { execute(); simp(); }
void outer(struct holder *holder, int32 *out, int32 *value) {
    owns mutex_live(&holder->mu);
    owns out[0..1];
    views value[0..1];
    requires separate(memory(out[0..1]), memory(holder->mu));
    ensures *out == *value;
} by { execute(); simp(); }
int32 run(struct holder *holder, int32 *out, int32 *value) {
    owns holder->mu;
    owns out[0..1];
    views value[0..1];
    requires separate(memory(out[0..1]), memory(holder->mu));
    requires aligned(&holder->mu, 8);
    ensures result == *value;
} by { execute(); simp(); }
```

```expect
pass
```
