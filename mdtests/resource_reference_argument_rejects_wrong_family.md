# Resource arguments must have the declared family

```click
resource cell(p: int32*) { field revision: int32; }
resource other(p: int32*) { field revision: int32; }
resource revision_record(p: int32*, target: cell(p)) { field revision: int32; }
void remember(int32* p) {
    owns target: other(p);
    owns record: revision_record(p, target);
}
```

```expect
fail: resource argument `target` is `other`, requires `cell`
```
