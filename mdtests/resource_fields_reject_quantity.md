# Quantities do not apply to field-bearing resources

Even a quantity of one cannot supply an identified member and its model fields.
Authority permits counting named members without making them anonymous quantities.

```click resource_semantics=authority
resource cell(p: int32*) {
    field model: List<int32>;
    owns p[0..1];
}

int32 read_cell(int32* p) {
    consumes 1 of cell(p);
}
```

```expect
fail: resource `cell` has fields; quantities require separately named members
```
