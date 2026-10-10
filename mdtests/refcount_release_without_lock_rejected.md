# A shared counter cannot be decremented without its mutex

The counter belongs to the control that the mutex holds. A releaser holding
only a use share of the mutex has no ownership of the counter until it
locks, so an unlocked decrement is refused rather than allowed to race.

```c filename=refcount_release_without_lock_rejected.c
#include <pthread.h>
#include <stddef.h>

struct object {
    pthread_mutex_t mu;
    int refs;
};

void object_release_unlocked(struct object *obj) {
    obj->refs = obj->refs - 1;
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
authorized resource reference(obj: struct object*) {}
authorized resource permit(obj: struct object*) {}
resource control(obj: struct object*) {
    field refs: int32;
    field slack: int32;
    owns obj->refs;
    owns authority(reference(obj));
    owns authority(permit(obj));
    fact obj->refs == refs;
    fact refs == count(reference(obj));
    fact slack == count(permit(obj));
    fact to_integer(refs) + to_integer(slack) == 3;
}

verifying "refcount_release_without_lock_rejected.c";

void object_release_unlocked(struct object *obj) {
    owns access: mutex_use(&obj->mu, control(obj));
    consumes reference(obj);
    produces permit(obj);
} by {
    execute();
    simp();
}
```

```expect
fail: missing resource fact `views obj->refs`
```
