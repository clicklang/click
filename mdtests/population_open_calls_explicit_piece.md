# An open control may lend an explicit piece to a helper

The helper borrows only the counter cell and preserves its value. The caller
keeps authority while its ordinary control is open and restores that control
after the unchanged C self-assignment and call.

```c filename=reopen.c
struct object { int32 refs; };
void inspect(struct object* obj) { }
void restored(struct object* obj) { obj->refs = obj->refs; inspect(obj); }
```

```click resource_semantics=authority
authorized resource reference(obj: struct object*) {}
resource control(obj: struct object*) {
    owns authority(reference(obj));
    owns obj->refs;
    fact obj->refs == count(reference(obj));
}
verifying "reopen.c";
void inspect(struct object* obj) {
    owns obj->refs;
    ensures obj->refs == old(obj->refs);
} by { execute(); simp(); }
void restored(struct object* obj) {
    owns control(obj);
} by {
    open(control(obj)) {
        step();
        step();
        execute();
    }
    simp();
}
```

```expect
pass
```
