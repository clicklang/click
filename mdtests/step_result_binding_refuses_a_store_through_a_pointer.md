# `let { result: name } = step()` refuses a store through a pointer

The result binding names the value a statement assigns to a scalar C local.
A store through a pointer, `p[0] = 3`, assigns no local, so the binding is
refused; a plain `step()` executes the store, and a later fact names the cell
itself, `p[0]`.

```c filename=step_result_binding_refuses_a_store_through_a_pointer.c
int32 store_three(int32* p) {
    p[0] = 3;
    return 0;
}
```

```click
verifying "step_result_binding_refuses_a_store_through_a_pointer.c";

int32 store_three(int32* p) {
    owns p[0..1];
    ensures p[0] == 3;
} by {
    let { result: stored } = step();
    execute();
    simp();
}
```

```expect
fail: `let { result: stored } = step()` requires a scalar assignment at the frontier
```
