# A family that owns an authorized child is not ordinary

`revision_record` is not itself authorized, but it owns a `cell`, which is.
Its named instance therefore reaches a population and keeps the checked
member rules: a definitional rewrite is refused.

```c filename=resource_reference_argument_owns.c
void remember(int32* p) { }
```

```click
verifying "resource_reference_argument_owns.c";
authorized resource cell(p: int32*) { field revision: int32; }
resource revision_record(p: int32*, target: cell(p)) {
    field revision: int32;
    owns target;
    fact target.revision == revision;
}
void remember(int32* p) {
    owns target: cell(p);
    ensures target.revision == old(target.revision);
} by {
    let record = fold(revision_record(p, target), { revision: target.revision }, { target: target });
    let { target: target } = unfold(record);
    execute();
    simp();
}
```

```expect
fail: named resource rewrite requires an ordinary memory body
```
