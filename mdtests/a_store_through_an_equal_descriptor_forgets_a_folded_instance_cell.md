# A store through a descriptor proven equal forgets a folded instance's cell

The negative of `a_store_keeps_a_cell_a_folded_instance_owns.md` when the
two descriptors are one. The contract requires `s == other`: no caller can
supply both `*other` and an instance owning `*s`. Raw entry admission sees the
instance's declared footprint and the stated alias, so it rejects the section
before the store. The C program and its preservation claim remain unchanged.

```c filename=a_store_through_an_equal_descriptor_forgets_a_folded_instance_cell.c
struct slot {
    int32* data;
    int32 at;
    int32 end;
};

int32 touch(struct slot* s, struct slot* other) {
    other->at = 7;
    return s->at;
}
```

```click
resource slot_span(s: struct slot*) {
    field at: int32;
    field end: int32;
    owns *s;
    fact s->at == at;
    fact s->end == end;
}

verifying "a_store_through_an_equal_descriptor_forgets_a_folded_instance_cell.c";

int32 touch(struct slot* s, struct slot* other) {
    requires s == other;
    owns r: slot_span(s);
    owns *other;
    ensures result == old(s->at);
}
```

```expect
fail: overlapping owned memory resource facts
```
