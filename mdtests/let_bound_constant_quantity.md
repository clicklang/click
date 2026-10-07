# A `let`-bound constant works as a resource quantity

`let` bindings are substituted before quantity lowering, so a constant bound
by `let` behaves exactly like writing the literal. (The retained `Let`
wrapper that used to reject this was sharing annotation only.)

```c filename=let_bound_constant_quantity.c
struct child {
    int32 refs;
};

void take_two(struct child* obj) {
    obj->refs = obj->refs - 2;
}
```

```click resource_semantics=authority
authorized resource child_ref(obj: struct child*) {}
resource control(obj: struct child*) {
    contains allocation(obj, sizeof(struct child));
    owns object(obj);
    owns authority(child_ref(obj));
    fact obj->refs == count(child_ref(obj));
}

verifying "let_bound_constant_quantity.c";

void take_two(struct child* obj) {
    owns control(obj);
    requires 2 <= obj->refs;
    let k: int32 = 2;
    consumes k of child_ref(obj);
} by {
    open(control(obj)) {
        unfold(2 of child_ref(obj));
        step();
    }
    execute(); simp();
}
```

```expect
pass
```
