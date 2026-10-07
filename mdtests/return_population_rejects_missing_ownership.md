# A post-return count cannot grant write authority during execution

Owning count authority and viewing the cell allows the initial count relation
to be read, but does not grant C write ownership. The unchanged increment is
rejected before any member birth; a promised post-state count cannot authorize
the earlier store.

```c filename=retain.c
struct object { int32 refs; };
struct object* retain(struct object* obj) { obj->refs += 1; return obj; }
```

```click resource_semantics=authority
authorized resource reference(obj: struct object*) {}
verifying "retain.c";
struct object* retain(struct object* obj) {
    requires count(reference(obj)) < 2147483647;
    owns authority(reference(obj));
    views obj->refs;
    requires obj->refs == count(reference(obj));
    produces reference(obj);
    ensures result == obj;
} by {
    step();
    fold(reference(obj));
    execute();
    simp();
}
```

```expect
fail: missing resource fact `owns obj[0..1]`
```
