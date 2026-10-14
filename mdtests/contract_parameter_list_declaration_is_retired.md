# The parameter-list contract declaration is retired

A named contract is the C declaration after `contract`, with each resource
handle declared by a named `owns` or `consumes` clause in the body. The
retired form, which listed handles before a `for` signature, is refused with
the replacement spelled out.

```click
resource marked_cell(p: int32*) {
    field revision: int32;
}

contract Read(cell: marked_cell(p)) for int32(int32* p) {
    owns cell;
}
```

```expect
fail: `contract Read(...) for ...` is retired; write the C declaration and declare each resource handle in the body
```
