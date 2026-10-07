# Opening a control cannot duplicate an authority already owned

A helper that receives the raw authority and a control containing the same
authority cannot open the control: its body's exclusive authority would
overlap the one already owned.

```c filename=authority_control_instance_duplicate_authority_rejected.c
struct object { int refs; };
void helper(struct object *obj) {}
```

```click resource_semantics=authority
verifying "authority_control_instance_duplicate_authority_rejected.c";
authorized resource reference(obj: struct object*) {}
resource control(obj: struct object*) {
    field refs: int32;
    owns obj->refs;
    owns authority(reference(obj));
    fact obj->refs == refs;
    fact refs == count(reference(obj));
}
void helper(struct object* obj) {
    owns authority(reference(obj));
    owns c: control(obj);
} by {
    unfold(c);
    execute();
    simp();
}
```

```expect
fail: instance body overlaps existing ownership
```
