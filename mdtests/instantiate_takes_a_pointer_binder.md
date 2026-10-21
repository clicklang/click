# instantiate takes a pointer binder

A pointer binder takes a pointer of its type, here the theorem's parameter.

```c filename=instantiate_takes_a_pointer_binder.c
void unused(void) {}
```

```click
verifying "instantiate_takes_a_pointer_binder.c";

function same(p: int32*, q: int32*) -> bool { p == q }

theorem ptr(q: int32*) {
    requires forall (p: int32*) { same(p, p) };
    ensures same(q, q) by {
        instantiate(forall (p: int32*) { same(p, p) }, q);
    }
}
```

```expect
pass
```
