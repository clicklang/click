# A proof binder cannot hide a C variable

In an execution proof, `step()` and `at(...)` keep reading the program's
variables. A proof binder that took the name of the C parameter `p` would
make `p` in the proof's propositions mean the binder while execution still
reads the parameter, so the binder is refused.

```c filename=hide_parameter.c
void remember(int32* p) { }
```

```click
verifying "hide_parameter.c";
resource cell(p: int32*) { field revision: int32; }
void remember(int32* p) {
    owns target: cell(p);
    ensures target.revision == old(target.revision);
} by {
    let { revision: p } = unfold(target);
    let target = fold(cell(p), { revision: p });
    execute();
    simp();
}
```

```expect
fail: `p` names a C variable here; a proof binder cannot hide it
```
