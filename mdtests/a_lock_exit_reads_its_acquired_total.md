# A locked helper reads its acquired total at the lock's exit

`release` locks the object's mutex. The lock hands back `control(obj)`,
which owns the population's authority, so the count can be read while the
control is still folded. The total the lock acquired is
`at(statement(0).exit, count(reference(obj)))`, the count once the lock
returns. After the helper spends its member, the counter is one less than
that total.

```c filename=a_lock_exit_reads_its_acquired_total.c
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

```click
target "x86_64-unknown-linux-gnu";
runtime "modeled-pthread";
verifying "a_lock_exit_reads_its_acquired_total.c";
authorized resource reference(obj: struct object*) {}
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
    let { guard: guard, state: state } = step(pthread_mutex_lock, { access: access });
    have count(reference(obj)) == at(statement(0).exit, count(reference(obj))) by known();
    unfold(state);
    unfold(reference(obj));
    step();
    have (obj->refs as int32) == ((at(statement(0).exit, count(reference(obj))) - 1) as int32);
    let restored = fold(control(obj), { refs: obj->refs });
    step(pthread_mutex_unlock, { access: access, guard: guard, state: restored });
    step();
    solve();
}
int32 run() {
    ensures result == -1 or result == 0;
} by {
    step();
    step();
    branch { true => { step(); solve(); } false => {} }
    step();
    fold(authority(reference(obj)));
    fold(reference(obj));
    let control = fold(control(obj), { refs: 1 });
    let { lifetime: lifetime } = step(pthread_mutex_init, { state: control });
    step(release, { access: lifetime });
    step(pthread_mutex_destroy, { lifetime: lifetime });
    unfold(control);
    have count(reference(obj)) == 0;
    unfold(authority(reference(obj)));
    step();
    step();
    solve();
}
```

```expect
pass
```
