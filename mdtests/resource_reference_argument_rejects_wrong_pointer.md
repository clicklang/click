# Resource reference arguments preserve their dependent pointer

The wrapper records a revision and refers to the exact named cell. Passing the
cell does not consume it or add its ownership to the wrapper's body.

```c filename=resource_reference_argument.c
void remember(int32* p, int32* q) { }
```

```click
verifying "resource_reference_argument.c";
resource cell(p: int32*) { field revision: int32; }
resource revision_record(p: int32*, target: cell(p)) {
    field revision: int32;
}
void remember(int32* p, int32* q) {
    owns target: cell(q);
    requires p != q;
    ensures target.revision == old(target.revision);
} by {
    let record = fold(revision_record(p, target), { revision: target.revision });
    unfold(record);
    execute();
    simp();
}
```

```expect
fail: Requires target: cell(p)
```
