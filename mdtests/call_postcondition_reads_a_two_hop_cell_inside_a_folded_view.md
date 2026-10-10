# Call postcondition reads a two-hop cell inside a folded view

`get` returns `s->pool->data[0]` and promises the caller that value,
spelled `old(s->pool->data[0])`. The caller `read_slot` lends only
`*s` and the folded `pool_state(s->pool)`, so the `data` field and its cell
are not directly readable in the caller's state. The call rule must evaluate
the postcondition's two-hop index place there, keep the path on which the
`data` load is not available, and still verify. This catches an lvalue
evaluator that mishandles an indexed place whose base pointer load fails.

```c filename=call_postcondition_reads_a_two_hop_cell_inside_a_folded_view.c
struct pool { int32* data; };
struct slot { struct pool* pool; };

int32 get(struct slot* s) {
    return s->pool->data[0];
}

int32 read_slot(struct slot* s) {
    return get(s);
}
```

```click
resource pool_state(pool: struct pool*) {
    owns pool->data;
    owns pool->data[0..1];
}

verifying "call_postcondition_reads_a_two_hop_cell_inside_a_folded_view.c";

int32 get(struct slot* s) {
    views *s;
    views pool_state(s->pool);
    ensures result == old(s->pool->data[0]);
} by {
    unfold(pool_state(s->pool));
    execute();
    simp();
}

int32 read_slot(struct slot* s) {
    views *s;
    views pool_state(s->pool);
} by {
    execute();
    simp();
}
```

```expect
pass
```
