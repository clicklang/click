# An unfolded scalar field remains an ordinary resource argument

```c filename=resource_child_pure_arguments_scalar.c
int32 read_value(int32* p) { return *p; }
```
```click
verifying "resource_child_pure_arguments_scalar.c";
resource cell(p: int32*, index: int32) {
    field value: int32;
    owns p[0..1];
    fact p[0] == value;
    fact value == index;
}
resource holder(p: int32*) {
    field value: int32;
    owns child: cell(p, value);
    fact child.value == value;
}
int32 read_value(int32* p) {
    owns root: holder(p);
    ensures result == old(root.value);
    ensures root.value == old(root.value);
} by {
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
