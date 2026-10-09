# A worker acquires a protected resource with a named child

The protected control owns one field directly and another through a named
child. Acquisition hands out a fresh instance whose unfolding binds the child,
and the worker refolds both before it unlocks.

```c filename=mutex_protected_named_child.c
#include <pthread.h>
struct pair { pthread_mutex_t mu; int a; int b; };
void copy_across(struct pair *p) {
    pthread_mutex_lock(&p->mu);
    p->b = p->a;
    pthread_mutex_unlock(&p->mu);
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "mutex_protected_named_child.c";
resource cell(p: struct pair*) {
    field v: int32;
    owns p->b;
    fact p->b == v;
}
resource pair_state(p: struct pair*) {
    field a: int32;
    field b: int32;
    owns p->a;
    owns second: cell(p);
    fact p->a == a;
    fact second.v == b;
}
void copy_across(struct pair *p) {
    owns access: mutex_use(&p->mu, pair_state(p));
} by {
    let { guard: guard, state: state } = step(pthread_mutex_lock(&p->mu), { access: access });
    let { a: a, b: b, second: second } = unfold(state);
    unfold(second);
    step();
    let copied = fold(cell(p), { v: p->b });
    let restored = fold(pair_state(p), { a: p->a, b: p->b }, { second: copied });
    step(pthread_mutex_unlock(&p->mu), { access: access, guard: guard, state: restored });
    step();
    simp();
}
```

```expect
pass
```
