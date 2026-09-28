# An ordinary call preserves resource arguments through its binder map

The caller and callee use different names for both instances. The record still
refers to the exact cell selected by the call's explicit binder map.

```c filename=resource_reference_argument_call.c
void preserve(int32* p) { }
void remember(int32* p) { preserve(p); }
```

```click
verifying "resource_reference_argument_call.c";
resource cell(p: int32*) { field revision: int32; }
resource revision_record(p: int32*, target: cell(p)) { field revision: int32; }
void preserve(int32* p) {
    owns c: cell(p);
    owns r: revision_record(p, c);
    ensures c.revision == old(c.revision);
    ensures r.revision == old(r.revision);
} by { execute(); simp(); }
void remember(int32* p) {
    owns target: cell(p);
    ensures target.revision == old(target.revision);
} by {
    let record = fold(revision_record(p, target), { revision: target.revision });
    step(preserve(p), { c: target, r: record });
    unfold(record);
    execute();
    simp();
}
```

```expect
pass
```
