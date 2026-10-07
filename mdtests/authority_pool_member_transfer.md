# Implicit local scalar access does not supply transferable private ownership

The recovered prototype retains its original C. Its first member fold is refused:
implicit local scalar access is not an explicit transferable owned range. This
is the same storage boundary retained by the field-free stack-object control.

```c filename=authority_pool_member_transfer.c
void move_slot() {
    int32 source = 0;
    int32 destination = 0;
    int32 cell = 0;
    cell = 1;
}
```

```click resource_semantics=authority
verifying "authority_pool_member_transfer.c";
authorized resource slot(pool: int32*, cell: int32*) {
    field label: int32;
    owns cell[0..1];
}
void move_slot() { ensures 1 == 1; } by {
    step();
    step();
    step();
    step();
    step();
    step();
    fold(authority(slot(&source, _)));
    fold(authority(slot(&destination, _)));
    let original = fold(slot(&source, &cell), { label: 42 });
    have count(slot(&source, _)) == 1 by simp;
    have count(slot(&destination, _)) == 0 by simp;
    let { label: saved } = unfold(original);
    let moved = fold(slot(&destination, &cell), { label: saved });
    have moved.label == 42 by simp;
    have count(slot(&source, _)) == 0 by simp;
    have count(slot(&destination, _)) == 1 by simp;
    unfold(moved);
    unfold(authority(slot(&source, _)));
    unfold(authority(slot(&destination, _)));
    execute();
    simp();
}
```

```expect
fail: fold requires ownership of the complete instance body
```
