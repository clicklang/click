# Initialization deposits an authority-bearing control in a mutex

Checked initialization deposits an ordinary control that owns the counter
cell and the population authority. Locking returns that control with its
guard; inside the critical section the proof creates a member under the
returned authority and observes the count. Unlocking requires the control
folded again with its facts restored. Destruction returns it, so the creator
can spend the member, retire the authority, and free the object. No
counted-population mutex custody is involved.

```c filename=authority_mutex_control_deposit.c
#include <pthread.h>
struct object { pthread_mutex_t mu; int refs; };
int run(void) {
    struct object *obj = malloc(sizeof(struct object));
    if (obj == 0) return -1;
    obj->refs = 0;
    pthread_mutex_init(&obj->mu, 0);
    pthread_mutex_lock(&obj->mu);
    obj->refs = obj->refs + 1;
    pthread_mutex_unlock(&obj->mu);
    pthread_mutex_destroy(&obj->mu);
    free(obj);
    return 0;
}
```

```click resource_semantics=authority
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "authority_mutex_control_deposit.c";
authorized resource reference(obj: struct object*) {}

resource control(obj: struct object*) {
    field refs: int32;
    owns obj->refs;
    owns authority(reference(obj));
    fact obj->refs == refs;
    fact refs == count(reference(obj));
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
    step();
    unfold(control);
    step();
    fold(reference(obj));
    have count(reference(obj)) == 1 by simp;
    let control = fold(control(obj), { refs: 1 });
    step();
    step(pthread_mutex_destroy(&obj->mu), { lifetime: lifetime });
    unfold(control);
    unfold(reference(obj));
    unfold(authority(reference(obj)));
    step();
    step();
    simp();
}
```

```expect
pass
```
