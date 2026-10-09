# A pure function describes a field-bearing count without granting authority

The function precedes the resource to check forward declaration resolution.

```click
function population(p: int32*) -> List<int32> {
    List<int32>::Cons(count(cell(p)), List<int32>::Nil)
}

authorized resource cell(p: int32*) {
    field model: List<int32>;
    owns p[0..1];
}
```

```expect
pass
```
