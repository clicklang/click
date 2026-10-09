# An unfold names the child it leaves unbound

Unfolding a resource with a named child must bind that child. The refusal
names the child and the binding to write.

```c filename=named_child_unfold_without_binding_rejected.c
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
verifying "named_child_unfold_without_binding_rejected.c";
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
    let { a: a, b: b } = unfold(state);
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
fail: unfold of `pair_state` must bind its named child `second`
```
