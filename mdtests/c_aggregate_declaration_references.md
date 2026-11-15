# Aggregate declaration references retain places and pointer fields

A declaration reference names the struct object, including its fields and the
C pointer value stored in a field. Its byte-array backing does not make it an
array expression, and reading a projection preserves the selected object.

```c filename=aggregate_declarations.c
struct item { int32* pointer; int32 value; };
int32 read_item(int32 x) {
    struct item object;
    object.value = x;
    object.pointer = &object.value;
    return *object.pointer;
}
```

```click
verifying "aggregate_declarations.c";

int32 read_item(int32 x) {
    ensures result == old(x);
} by {
    step_until(statement(3));
    have read_item.local(0).value == read_item.parameter(0) by known();
    have *read_item.local(0).pointer == read_item.parameter(0) by known();
    step_until(function.exit);
}
```

```expect
pass
```
