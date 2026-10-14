# A pure result must match the child's declared pointer type

```c filename=resource_child_pure_arguments_wrong_type.c
void empty(int8* p) {}
```
```click
verifying "resource_child_pure_arguments_wrong_type.c";
function byte_pointer(p: int8*) -> int8* { p }
resource cell(p: int32*) { field value: int32; owns p[0..1]; fact p[0] == value; }
resource holder(p: int8*) {
    field value: int32;
    owns child: cell(byte_pointer(p));
    fact child.value == value;
}
void empty(int8* p) {
    owns root: holder(p);
    ensures root.value == old(root.value);
} by { let { child: c } = unfold(root); execute(); }
```
```expect
fail: recursive child argument type mismatch
```
