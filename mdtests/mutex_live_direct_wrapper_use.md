# A direct lifetime input survives wrapper transport and use lending

```c filename=lifetime_inputs.c
#include <pthread.h>
struct holder { pthread_mutex_t mu; };
void wrapped(struct holder *holder) {}
void borrow(struct holder *holder) {}
void keep(struct holder *holder) {
    wrapped(holder);
    borrow(holder);
    wrapped(holder);
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
resource lifetime(holder: struct holder*) {
    field tag: int32;
    owns mutex_live(&holder->mu);
}
verifying "lifetime_inputs.c";

void wrapped(struct holder *holder) {
    owns life: lifetime(holder);
} by { unfold(life); fold(life); execute(); simp(); }
void borrow(struct holder *holder) {
    owns mutex_use(&holder->mu);
} by { execute(); simp(); }
void keep(struct holder *holder) {
    owns mutex_live(&holder->mu);
} by {
    let life = fold(lifetime(holder), { tag: 0 });
    step(wrapped(holder), { life: life });
    unfold(life);
    step(borrow(holder), {});
    let next = fold(lifetime(holder), { tag: 0 });
    step(wrapped(holder), { life: next });
    unfold(next);
    step();
    simp();
}
```

```expect
pass
```
