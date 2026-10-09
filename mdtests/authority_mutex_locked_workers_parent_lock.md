# The creator may lock while locked workers are outstanding

The creator locks and unlocks the mutex between the creates and the joins
without opening the control. That holds no count fact, so it needs no current
total, and the workers' changes still apply at their joins.

```c filename=authority_mutex_locked_workers_parent_lock.c
#include <pthread.h>
#include <stddef.h>
struct object { pthread_mutex_t mu; int refs; };
void *release(void *argument) {
    struct object *obj = argument;
    pthread_mutex_lock(&obj->mu);
    obj->refs = obj->refs - 1;
    pthread_mutex_unlock(&obj->mu);
    return NULL;
}
int run(void) {
    pthread_t a;
    pthread_t b;
    struct object *obj = malloc(sizeof(struct object));
    if (obj == 0) return -1;
    obj->refs = 2;
    pthread_mutex_init(&obj->mu, 0);
    if (pthread_create(&a, NULL, release, obj) != 0) {
        pthread_mutex_destroy(&obj->mu);
        free(obj);
        return 0;
    }
    if (pthread_create(&b, NULL, release, obj) != 0) {
        pthread_join(a, NULL);
        pthread_mutex_destroy(&obj->mu);
        free(obj);
        return 0;
    }
    pthread_mutex_lock(&obj->mu);
    pthread_mutex_unlock(&obj->mu);
    pthread_join(a, NULL);
    pthread_join(b, NULL);
    pthread_mutex_destroy(&obj->mu);
    free(obj);
    return 1;
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "authority_mutex_locked_workers_parent_lock.c";
authorized resource reference(obj: struct object*) {}
resource control(obj: struct object*) {
    field refs: int32;
    owns obj->refs;
    owns authority(reference(obj));
    fact obj->refs == refs;
    fact refs == count(reference(obj));
}
void* release(void* argument) {
    owns access: mutex_use(&((struct object*)argument)->mu, control((struct object*)argument));
    consumes reference((struct object*)argument);
} by {
    step();
    step();
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
    ensures result == -1 or result == 0 or result == 1;
} by {
    step();
    step();
    step();
    step();
    branch then { step(); simp(); } else {}
    step();
    fold(authority(reference(obj)));
    fold(reference(obj));
    fold(reference(obj));
    let control = fold(control(obj), { refs: 2 });
    let { lifetime: lifetime } = step(pthread_mutex_init(&obj->mu, 0), { state: control });
    step();
    branch then {
        step(pthread_mutex_destroy(&obj->mu), { lifetime: lifetime });
        unfold(control);
        unfold(reference(obj));
        unfold(reference(obj));
        have count(reference(obj)) == 0;
        unfold(authority(reference(obj)));
        step();
        step();
        simp();
    } else {}
    step();
    branch then {
        step();
        step(pthread_mutex_destroy(&obj->mu), { lifetime: lifetime });
        unfold(control);
        unfold(reference(obj));
        have count(reference(obj)) == 0;
        unfold(authority(reference(obj)));
        step();
        step();
        simp();
    } else {}
    step();
    step();
    step();
    step();
    step(pthread_mutex_destroy(&obj->mu), { lifetime: lifetime });
    unfold(control);
    have count(reference(obj)) == 0;
    unfold(authority(reference(obj)));
    step();
    step();
    simp();
}
```

```expect
pass
```
