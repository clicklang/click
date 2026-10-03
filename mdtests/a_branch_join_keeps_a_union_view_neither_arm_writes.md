# A branch join keeps a union view neither arm writes

The positive control for the joins that forget typed union views. Neither
arm of the `if (c)` below writes memory, so the join keeps the view of
`source.payload.number` copied from `g`, and the load after the join reads
the copied value.

```c filename=a_branch_join_keeps_a_union_view_neither_arm_writes.c
union payload {
    int32 number;
    int32* pointer;
};

struct packet {
    int32 tag;
    union payload payload;
};

struct packet g;

int32 branch_writes_nothing(int32 c) {
    struct packet source;
    int32* p;
    source = g;
    p = &source.payload.number;
    if (c) {
        c = 2;
    }
    return source.payload.number;
}
```

```click
verifying "a_branch_join_keeps_a_union_view_neither_arm_writes.c";

int32 branch_writes_nothing(int32 c) {
    owns g.tag;
    owns g.payload.number;
    requires g.payload.number == 3;
    ensures result == 3;
} by {
    step();
    step();
    step();
    step();
    branch {
        ensuring {
            fact 1 == 1;
        }
        then {
            step();
        }
        else {
        }
    }
    execute();
    simp();
}
```

```expect
pass
```
