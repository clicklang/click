# A named contract declares a resource handle with a named clause

`owns cell: marked_cell(p);` both declares the handle `cell` and requires and
returns ownership of the instance a call binds to it. A call selects the
contract with `step(Read, { cell: instance })`. This fixture checks the
declaration, not cross-function resource transport.

```click
resource marked_cell(p: int32*) {
    field revision: int32;
}

contract int32 Read(int32* p) {
    owns cell: marked_cell(p);
    ensures cell.revision == old(cell.revision);
}
```

```expect
pass
```
