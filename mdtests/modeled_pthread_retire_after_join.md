# The parent retires a lent population after join

The creator establishes a population on a fresh object and lends its authority
to a worker. Join returns the authority, so the creator retires the population
and frees the object afterward.

```c filename=modeled_pthread_retire_after_join.c
#include <pthread.h>
#include <stddef.h>
struct object { int refs; };
void *worker(void *argument) { return NULL; }
int run(void) {
    struct object *obj = malloc(sizeof(struct object));
    if (obj == 0) return -1;
    pthread_t handle;
    if (pthread_create(&handle, NULL, worker, obj) != 0) {
        free(obj);
        return 0;
    }
    (void)pthread_join(handle, NULL);
    free(obj);
    return 1;
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "modeled_pthread_retire_after_join.c";
authorized resource reference(obj: struct object*) {}
void* worker(void* argument) {
    owns authority(reference((struct object*)argument));
} by { execute(); simp(); }
int32 run() {
    ensures result == -1 or result == 0 or result == 1;
} by {
    step();
    step();
    branch then { step(); simp(); } else {}
    fold(authority(reference(obj)));
    step();
    step();
    branch then {
        unfold(authority(reference(obj)));
        step();
        step();
        simp();
    } else {}
    step();
    unfold(authority(reference(obj)));
    step();
    step();
    simp();
}
```

```expect
pass
```
