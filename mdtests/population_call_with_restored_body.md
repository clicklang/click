# A restored control body may cross a call boundary

Closing the ordinary control restores both its counter relation and custody.
The helper can then borrow the whole closed control. No population member
implicitly grants access to the counter cell. The C is unchanged.

```c filename=reopen.c
struct object { int32 refs; };
void inspect(struct object* obj) { }
void restored(struct object* obj) { obj->refs = obj->refs; inspect(obj); }
```

```click resource_semantics=authority
resource reference(obj: struct object*) {}
resource control(obj: struct object*) {
    owns authority(reference(obj));
    owns obj->refs;
    fact obj->refs == count(reference(obj));
}
verifying "reopen.c";
void inspect(struct object* obj) {
    owns control(obj);
} by { execute(); simp(); }
void restored(struct object* obj) {
    owns control(obj);
} by {
    open(control(obj)) {
        step();
    }
    execute();
    simp();
}
```

```expect
pass
```
