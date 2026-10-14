# Scalar pure calls in child resource indices

```c filename=resource_child_pure_arguments_scalar.c
int32 read_value(int32* p) { return *p; }
```
```click
verifying "resource_child_pure_arguments_scalar.c";
function scalar_index(value: int32) -> int32 { value }
resource cell(p: int32*, index: int32) {
    field value: int32;
    owns p[0..1];
    fact p[0] == value;
    fact value == index;
}
resource holder(p: int32*) {
    field value: int32;
    owns child: cell(p, scalar_index(value));
    fact child.value == value;
}
int32 read_value(int32* p) {
    owns root: holder(p);
    ensures result == old(root.value);
    ensures root.value == old(root.value);
} by {
    have scalar_index(root.value) == root.value by { unfold(scalar_index(root.value)); normalize(); }
    let { value: v, child: child } = unfold(root);
    unfold(child);
    execute();
    let child = fold(cell(p, v), { value: v });
    let root = fold(holder(p), { value: v }, { child: child });
    simp();
}
```
```expect
pass
```
