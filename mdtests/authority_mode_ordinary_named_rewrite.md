# An ordinary named resource folds and unfolds in authority mode

Neither `cell` nor `revision_record` is an `authorized resource`, and neither
reaches one, so the named instance of `revision_record` folds and unfolds by
its definition in an authority-mode project.

```c filename=resource_reference_argument_owns.c
void remember(int32* p) { }
```

```click
verifying "resource_reference_argument_owns.c";
resource cell(p: int32*) { field revision: int32; }
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
pass
```
