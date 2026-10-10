# Two opaque reallocating calls do not carry an unstated value

`box_renew` is an external function that may replace `box->data`; its
contract hands back `*box` and the cell it points to, separate as on entry,
and says nothing about the cell's value. After two calls, the read of
`box->data[0]` is readable but the claim that it equals the entry value is
refused. Naming that read walks back across the second call's havoc, which
needs `*box` separate from the new cell: the stated `separate` fact supplies
it with `*box` on its left side and the cell on its right. This is the
opaque, resource-free form of
`consecutive_reallocating_calls_do_not_carry_an_unstated_value.md`.

```c filename=two_opaque_reallocating_calls_do_not_carry_an_unstated_value.c
struct box {
    int32* data;
};

extern void box_renew(struct box* box);

int32 box_cycle(struct box* box) {
    box_renew(box);
    box_renew(box);
    return box->data[0];
}
```

```click
verifying "two_opaque_reallocating_calls_do_not_carry_an_unstated_value.c";

extern void box_renew(struct box* box) {
    consumes *box;
    consumes box->data[0..1];
    requires separate(memory(*box), memory(box->data[0..1]));
    produces *box;
    produces box->data[0..1];
    ensures separate(memory(*box), memory(box->data[0..1]));
}

int32 box_cycle(struct box* box) {
    consumes *box;
    consumes box->data[0..1];
    requires separate(memory(*box), memory(box->data[0..1]));
    produces *box;
    produces box->data[0..1];
    ensures result == old(box->data[0]);
} by {
    execute();
    simp();
}
```

```expect
fail: unclosed goal
```
