# Closing a viewed resource scope at return preserves the named refold frontier

```c filename=view_scope.c
void inspect(int32* p) { }
```

```click
verifying "view_scope.c";
resource cell(p: int32*) { views p[0..1]; }
resource marker() { field value: int32; }
void inspect(int32* p) {
    views cell(p);
    produces tag: marker();
    ensures tag.value == 1;
} by {
    open(cell(p)) { execute(); }
    let tag = fold(marker(), { value: 1 });
    simp();
}
```

```expect
pass
```
