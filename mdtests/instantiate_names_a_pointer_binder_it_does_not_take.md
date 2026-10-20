# instantiate refuses a pointer binder

`instantiate` takes an `int32` or `uint64` binder. The binder's type is
checked before the argument is read, so the refusal names it, whatever the
argument's spelling, and points to stating the instance as a theorem.

```c filename=instantiate_names_a_pointer_binder_it_does_not_take.c
void unused(void) {}
```

```click
verifying "instantiate_names_a_pointer_binder_it_does_not_take.c";

theorem t(q: int32*) {
    requires forall (p: int32*) { p == p };
    ensures q == q by {
        instantiate(forall (p: int32*) { p == p }, q);
    }
}
```

```expect
fail: `p` is a pointer binder
```
