# A simple closer cannot discard the final population allocation

The final release restores the logical count but omits `free`. Completing
its pure postcondition with a simple tactic must still check the allocation
obligation when applying the return-resource exchange.

```c filename=leak.c
struct object { int32 refs; };
void release(struct object* obj) { obj->refs = 0; }
```

```click resource_semantics=authority
authorized resource reference(obj: struct object*) {}

resource control(obj: struct object*) {
    owns allocation(obj, sizeof(struct object));
    owns *obj;
    owns authority(reference(obj));
    fact obj->refs == count(reference(obj));
}
verifying "leak.c";
void release(struct object* obj) {
    requires obj->refs == 1;
    consumes control(obj);
    consumes reference(obj);
    ensures 0 == 0;
} by {
    unfold(control(obj));
    unfold(reference(obj));
    unfold(authority(reference(obj)));
    execute();
    normalize();
}
```

```expect
fail: live allocation obligation
```
