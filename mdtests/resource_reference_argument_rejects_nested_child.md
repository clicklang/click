# Unsupported nested child metadata cannot erase resource arguments

```c filename=resource_reference_argument_rejects_nested_child.c
void preserve() { }
```

```click
verifying "resource_reference_argument_rejects_nested_child.c";
resource cell() { field revision: int32; }
resource record(target: cell()) { field revision: int32; }
resource outer(target: cell()) {
    field revision: int32;
    owns nested: record(target);
    fact nested.revision == revision;
}
void preserve() { owns target: cell(); owns envelope: outer(target); }
```

```expect
fail: owned child `nested` passes resource arguments; nested resource-argument child ownership is not supported yet
```
