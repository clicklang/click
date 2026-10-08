# An ordinary read-only helper borrows protected memory after acquisition

```c filename=mutex_body_helper.c
#include <pthread.h>
struct counter { pthread_mutex_t mutex; unsigned int value; };
unsigned int read_value(struct counter *p) { return p->value; }
unsigned int read_locked(struct counter *p) {
    pthread_mutex_lock(&p->mutex);
    unsigned int result = read_value(p);
    pthread_mutex_unlock(&p->mutex);
    return result;
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "mutex_body_helper.c";
abstract resource contribution(p: struct counter*);
resource counter_state(p: struct counter*) {
    field value: uint32;
    owns p->value;
    fact p->value == value;
}
uint32 read_value(struct counter* p) {
    views p->value;
    ensures result == p->value;
} by { execute(); simp(); }
uint32 read_locked(struct counter* p) {
    owns contribution(p);
    owns access: mutex_use(&p->mutex, counter_state(p));
} by {
    let { guard: guard, state: state } = step(pthread_mutex_lock(&p->mutex), { access: access });
    unfold(state);
    step();
    step();
    let restored = fold(counter_state(p), { value: p->value });
    step(pthread_mutex_unlock(&p->mutex), { access: access, guard: guard, state: restored });
    step();
    simp();
}
```

```expect
pass
```
