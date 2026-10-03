# A loop keeps a union view outside its declared write set

The positive control for
`a_loop_that_writes_a_union_member_forgets_its_view.md`. The loop head
forgets the typed union views of `g2` as it forgets every cached value, but
the loop declares that it writes only `other`, so the load of
`g2.payload.number` after the loop reads across the loop to the copied
value, and `ensures result == 3` verifies.

```c filename=a_loop_keeps_a_union_view_outside_its_write_set.c
union payload {
    int32 number;
    int32* pointer;
};

struct packet {
    int32 tag;
    union payload payload;
};

struct packet g;
struct packet g2;
int32 other[4];

int32 loop_writes_other() {
    int32 i;
    g2 = g;
    i = 0;
    while (i < 4) {
        other[i] = 0;
        i = i + 1;
    }
    return g2.payload.number;
}
```

```click
verifying "a_loop_keeps_a_union_view_outside_its_write_set.c";

int32 loop_writes_other() {
    owns g.tag;
    owns g.payload.number;
    owns g2.tag;
    owns g2.payload.number;
    owns other[0..4];
    requires g.payload.number == 3;
    ensures result == 3;
} by {
    step();
    step();
    step();
    loop {
        owns other[0..4];
        decreases 4 - i;
        invariant i >= 0;
        invariant i <= 4;
    }
    execute();
    simp();
}
```

```expect
pass
```
