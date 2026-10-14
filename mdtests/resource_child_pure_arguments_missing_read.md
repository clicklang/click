# A pure child index does not grant unrelated read authority

```c filename=resource_child_pure_arguments_missing_read.c
int32 read_other(int32* p, int32* other) { return *other; }
```
```click
verifying "resource_child_pure_arguments_missing_read.c";
function model_pointer(p: int32*) -> int32* { p }
resource cell(p: int32*) { field value: int32; owns p[0..1]; fact p[0] == value; }
resource holder(p: int32*) {
    field value: int32;
    owns child: cell(model_pointer(p));
    fact child.value == value;
}
int32 read_other(int32* p, int32* other) {
    owns root: holder(p);
    ensures root.value == old(root.value);
} by {
    let { child: child } = unfold(root);
    unfold(child);
    execute();
}
```
```expect
fail: missing resource fact
```
