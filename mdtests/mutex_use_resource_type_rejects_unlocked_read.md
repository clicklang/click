# Naming the protected resource type does not grant its ownership

```c filename=mutex_use_resource_type_read.c
#include <pthread.h>
struct counter { pthread_mutex_t mu; unsigned int value; };
unsigned int read_counter(struct counter *counter) { return counter->value; }
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
resource counter_state(counter: struct counter*) {
    field value: uint32;
    owns counter->value;
    fact counter->value == value;
}
verifying "mutex_use_resource_type_read.c";
uint32 read_counter(struct counter *counter) {
    owns access: mutex_use(&counter->mu, counter_state(counter));
} by { execute(); simp(); }
```

```expect
fail: missing resource fact `views counter[10..11]`
```
