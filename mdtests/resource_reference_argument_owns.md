# Ownership of a resource argument is a separate body clause

The wrapper owns its argument only because its body says `owns target`. Its
revision field records the owned child model using the ordinary child rules.

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
