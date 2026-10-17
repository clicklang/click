# A loop writing through the struct forgets the union view it reaches

The loop writes the union member through a pointer to the whole struct,
`p[2]` with `p = (int32*)&source`, so no spelling of the store names the
member. The loop head forgets every cached value nothing protects, and a
typed union view is one of them: it used to survive, the load after the loop
read the copied 3, and the false `ensures result == 3` verified, although
`loop_writes_past_tag` returns 9.

The pointer designates the struct, not its first member, so the store stays
inside the object it points to; the companion
`a_loop_writing_past_a_sibling_field_forgets_the_union_view.md` reaches the
member through `&source.tag` and is refused at the store.

```c filename=a_loop_writing_through_the_struct_forgets_the_union_view.c
union payload {
    int32 number;
    int32* pointer;
};

struct packet {
    int32 tag;
    int32 pad;
    union payload payload;
};

struct packet g;

int32 loop_writes_past_tag() {
    struct packet source;
    int32* p;
    int32 i;
    source = g;
    p = (int32*)&source;
    i = 0;
    while (i < 2) {
        p[2] = 9;
        i = i + 1;
    }
    return source.payload.number;
}
```

```click
verifying "a_loop_writing_through_the_struct_forgets_the_union_view.c";

int32 loop_writes_past_tag() {
    owns g.tag;
    owns g.pad;
    owns g.payload.number;
    requires g.payload.number == 3;
    ensures result == 3;
} by {
    step();
    step();
    step();
    step();
    step();
    step();
    loop {
        decreases 2 - i;
        invariant i >= 0;
        invariant i <= 2;
    }
    execute();
    simp();
}
```

```expect
fail: left side evaluated to at(<state A>, source.payload.number), right side evaluated to 3
```
