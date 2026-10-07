# A standalone acquiring helper may open the acquired control

An acquiring helper's own proof receives a fresh control from the lock. Its
authority enters the helper's proof with a fresh total, bounded below only by
the members the helper owns, so the helper may open the control and observe
that total. It changes no member, so its contract declares no member effect,
and it refolds the control before returning it. The caller that established
the population opens the returned control under its own ledger.

```c filename=authority_mutex_control_helper_open.c
#include <pthread.h>
struct object { pthread_mutex_t mu; int refs; };
void acquire(struct object *obj) { pthread_mutex_lock(&obj->mu); }
void release(struct object *obj) { pthread_mutex_unlock(&obj->mu); }
int run(void) {
    struct object *obj = malloc(sizeof(struct object));
    if (obj == 0) return -1;
    obj->refs = 0;
    pthread_mutex_init(&obj->mu, 0);
    acquire(obj);
    obj->refs = obj->refs + 1;
    release(obj);
    acquire(obj);
    obj->refs = obj->refs - 1;
    release(obj);
    pthread_mutex_destroy(&obj->mu);
    free(obj);
    return 0;
}
```

```click resource_semantics=authority
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "authority_mutex_control_helper_open.c";
resource reference(obj: struct object*) {}

resource control(obj: struct object*) {
    field refs: int32;
    owns obj->refs;
    owns authority(reference(obj));
    fact obj->refs == refs;
    fact refs == count(reference(obj));
}

void acquire(struct object *obj) {
    owns access: mutex_use(&obj->mu, control(obj));
    produces guard: mutex_guard(&obj->mu);
    produces state: control(obj);
} by {
    let { guard: acquired, state: state } = step(pthread_mutex_lock(&obj->mu), { access: access });
    unfold(state);
    have count(reference(obj)) >= 0 by simp;
    let state = fold(control(obj), { refs: obj->refs });
    step();
    simp();
}

void release(struct object *obj) {
    owns access: mutex_use(&obj->mu, control(obj));
    consumes guard: mutex_guard(&obj->mu);
    consumes state: control(obj);
} by {
    step(pthread_mutex_unlock(&obj->mu), { access: access, guard: guard, state: state });
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
    let control = fold(control(obj), { refs: 0 });
    let { lifetime: lifetime } = step(pthread_mutex_init(&obj->mu, 0), { state: control });
    let { guard: first, state: entered } = step(acquire(obj), { access: lifetime });
    unfold(entered);
    step();
    fold(reference(obj));
    let retained = fold(control(obj), { refs: 1 });
    step(release(obj), { access: lifetime, guard: first, state: retained });
    let { guard: second, state: reentered } = step(acquire(obj), { access: lifetime });
    unfold(reentered);
    have count(reference(obj)) == 1 by simp;
    unfold(reference(obj));
    step();
    let released = fold(control(obj), { refs: 0 });
    step(release(obj), { access: lifetime, guard: second, state: released });
    step(pthread_mutex_destroy(&obj->mu), { lifetime: lifetime });
    unfold(released);
    unfold(authority(reference(obj)));
    step();
    step();
    simp();
}
```

```expect
pass
```
