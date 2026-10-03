# A retained population unit cannot lend its body outside the lock

```c filename=population_access.c
#include <pthread.h>
#include <stddef.h>
struct counter { pthread_mutex_t mutex; unsigned int value; };
unsigned int read_member(struct counter *p) { return p->value; }
unsigned int run(struct counter *p) {
    p->value = 3u;
    if (pthread_mutex_init(&p->mutex, NULL) != 0) return 0u;
    
    unsigned int result = read_member(p);
    
    (void)pthread_mutex_destroy(&p->mutex);
    return result;
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "population_access.c";
resource member(p: struct counter*) {
    owns p->value;
    fact p->value == count(member(p));
}
resource counter_state(p: struct counter*) {
    field retained: int32;
    owns retained of member(p);
    fact retained > 0;
}
uint32 read_member(struct counter* p) {
    owns member(p);
    ensures result == count(member(p));
} by { open(member(p)) { step(); } simp(); }
uint32 run(struct counter* p) {
    owns p->value;
    owns &p->mutex;
    requires aligned(&p->mutex, 8);
    ensures result == 0 or result == 3;
} by {
    step();
    fold(3 of member(p));
    let state = fold(counter_state(p), { retained: 1 });
    let { lifetime: lifetime } = step(pthread_mutex_init(&p->mutex, 0), { state: state });
    branch then { unfold(state); unfold(3 of member(p)); step(); simp(); } else {}
    
    step();
    step();
    
    step(pthread_mutex_destroy(&p->mutex), { lifetime: lifetime });
    unfold(state);
    unfold(3 of member(p));
    step();
    simp();
}
```

```expect
fail: Requires owns mutex_guard(&p->mutex)
```
