# A caller's counter fact is stale after a locked helper returns

The creator deposits the control with a counter of one. After `release`
spends the member under the lock, the control the creator recovers at
destruction states a counter of zero, so the stale `obj->refs == 1` fails.

```c filename=authority_mutex_locked_release_stale_rejected.c
#include <pthread.h>
struct object { pthread_mutex_t mu; int refs; };
void release(struct object *obj) {
    pthread_mutex_lock(&obj->mu);
    obj->refs = obj->refs - 1;
    pthread_mutex_unlock(&obj->mu);
}
int run(void) {
    struct object *obj = malloc(sizeof(struct object));
    if (obj == 0) return -1;
    obj->refs = 1;
    pthread_mutex_init(&obj->mu, 0);
    release(obj);
    pthread_mutex_destroy(&obj->mu);
    free(obj);
    return 0;
}
```

```click resource_semantics=authority
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "authority_mutex_locked_release_stale_rejected.c";
resource reference(obj: struct object*) {}
resource control(obj: struct object*) {
    field refs: int32;
    owns obj->refs;
    owns authority(reference(obj));
    fact obj->refs == refs;
    fact refs == count(reference(obj));
}
void release(struct object *obj) {
    owns access: mutex_use(&obj->mu, control(obj));
    consumes reference(obj);
} by {
    let { guard: guard, state: state } = step(pthread_mutex_lock(&obj->mu), { access: access });
    unfold(state);
    unfold(reference(obj));
    step();
    let restored = fold(control(obj), { refs: obj->refs });
    step(pthread_mutex_unlock(&obj->mu), { access: access, guard: guard, state: restored });
    step();
    simp();
}
int32 run() {
    ensures result == -1 or result == 0;
} by {
    step();
    step();
    branch then { step(); simp(); } else {}
    step();
    fold(authority(reference(obj)));
    fold(reference(obj));
    let control = fold(control(obj), { refs: 1 });
    let { lifetime: lifetime } = step(pthread_mutex_init(&obj->mu, 0), { state: control });
    step(release(obj), { access: lifetime });
    step(pthread_mutex_destroy(&obj->mu), { lifetime: lifetime });
    unfold(control);
    have obj->refs == 1 by simp;
    unfold(authority(reference(obj)));
    step();
    step();
    simp();
}
```

```expect
fail: `have obj->refs == 1` did not close its checked nested goal
```
