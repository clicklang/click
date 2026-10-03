```c filename=foreign.c
void wrap(int32* p, int32* other) {}
```

```click resource_semantics=authority
predicate is_zero(cell: int32*) { cell[0] == 0 }
resource zero_cell(cell: int32*, other: int32*) {
    owns cell[0..1];
    fact is_zero(other);
}
verifying "foreign.c";
void wrap(int32* p, int32* other) {
    owns authority(zero_cell(p, _));
    requires count(zero_cell(p, _)) == 0;
    requires is_zero(other);
    consumes p[0..1];
    owns other[0..1];
    produces zero_cell(p, other);
} by {
    unfold(is_zero);
    fold(zero_cell(p, other));
    execute(); simp();
}
```

```expect
fail: resource `zero_cell` fact reads `other[0]` without a covering contained memory resource
```
