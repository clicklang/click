# `guarded_by` is retired

A resource no longer names its mutex. The checked `pthread_mutex_init` step
deposits the resource it is given, and that is the association.

```c filename=guarded_by_retired.c
#include <pthread.h>
struct box { pthread_mutex_t mu; int value; };
void start(struct box *box) {
    pthread_mutex_init(&box->mu, 0);
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
resource box_state(box: struct box*) {
    field value: int32;
    guarded_by box->mu;
    owns box->value;
}

verifying "guarded_by_retired.c";

void start(struct box *box) {
    owns box->mu;
    requires aligned(&box->mu, 8);
} by {
    execute();
}
```

```expect
fail: `guarded_by` is retired
```
