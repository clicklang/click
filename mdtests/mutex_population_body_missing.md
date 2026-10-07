# Contribution units and mutex_use do not supply protected memory to a helper

```c filename=mutex_population_body_missing.c
#include <pthread.h>
struct counter { pthread_mutex_t mutex; unsigned int value; };
unsigned int read_value(struct counter *p) { return p->value; }
unsigned int read_without_lock(struct counter *p) { return read_value(p); }
```

```click resource_semantics=authority
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "mutex_population_body_missing.c";
abstract resource contribution(p: struct counter*);
resource counter_state(p: struct counter*) {
    field value: uint32;
    owns p->value;
    fact p->value == value;
}
uint32 read_value(struct counter* p) {
    owns p->value;
    ensures result == p->value;
} by { execute(); simp(); }
uint32 read_without_lock(struct counter* p) {
    owns contribution(p);
    owns access: mutex_use(&p->mutex, counter_state(p));
} by { execute(); simp(); }
```

```expect
fail: missing resource fact `owns p[10..12]`
```
