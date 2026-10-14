# Child resource indices still require C values

```c filename=resource_child_pure_arguments_non_c.c
void empty(void) {}
```
```click
verifying "resource_child_pure_arguments_non_c.c";
spec enum Model { Empty }
function model() -> Model { Model::Empty }
resource cell(p: int32*) { field value: int32; owns p[0..1]; fact p[0] == value; }
resource holder() {
    field value: int32;
    owns child: cell(model());
    fact child.value == value;
}
void empty() { ensures 1 == 1; } by { execute(); simp(); }
```
```expect
fail: function `model` does not return a C value
```
