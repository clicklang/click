# An ordinary family folds by its definition in authority mode

Population accounting covers only families declared `authorized resource`.
`cell` is an ordinary resource, so in an authority-mode project it unfolds
and folds by its definition, as it does without authority semantics; no
member is created or destroyed.

```c filename=ordinary_family_fold.c
struct object { int32 refs; };
void reset(struct object* obj) {
    obj->refs = 0;
}
```

```click
resource cell(obj: struct object*) {
    owns obj->refs;
}

verifying "ordinary_family_fold.c";

void reset(struct object* obj) {
    owns cell(obj);
} by {
    unfold(cell(obj));
    step();
    fold(cell(obj));
    execute();
    simp();
}
```

```expect
pass
```
