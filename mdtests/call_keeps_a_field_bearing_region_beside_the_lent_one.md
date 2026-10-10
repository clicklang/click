# A call keeps a field-bearing region beside the lent one

`pool_slot` is a field-bearing region that owns its descriptor and
`pool->data[at..end]`. `two_puts` writes `11` through `first` and then
`22` through `second`, lending only `second`'s region to the second call,
and claims the first value survives. The caller keeps `first`'s region, so
the call havoc must keep its cell, which is addressed through a reloaded
`pool->data` rather than the base spelling the region was folded with;
`simp` relates the two through `put`'s `pool->data == old(pool->data)`.

```c filename=call_keeps_a_field_bearing_region_beside_the_lent_one.c
struct pool { int32* data; };
struct slot { int32 at; int32 end; };

void put(struct pool* pool, struct slot* s, int32 value) {
    pool->data[s->at] = value;
}

void two_puts(struct pool* pool, struct slot* first, struct slot* second) {
    put(pool, first, 11);
    put(pool, second, 22);
}
```

```click
resource pool_slot(s: struct slot*, pool: struct pool*) {
    field at: int32;
    field end: int32;
    owns *s;
    owns pool->data[at..end];
    fact s->at == at;
    fact s->end == end;
    fact 0 <= at;
    fact at < end;
}

verifying "call_keeps_a_field_bearing_region_beside_the_lent_one.c";

void put(struct pool* pool, struct slot* s, int32 value) {
    owns pool->data;
    owns r: pool_slot(s, pool);

    ensures r.at == old(r.at);
    ensures r.end == old(r.end);
    ensures pool->data == old(pool->data);
    ensures pool->data[s->at] == value;
} by {
    let { at: a, end: e } = unfold(r);
    execute();
    let r = fold(pool_slot(s, pool), { at: a, end: e });
    simp();
}

void two_puts(struct pool* pool, struct slot* first, struct slot* second) {
    owns pool->data;
    owns a: pool_slot(first, pool);
    owns b: pool_slot(second, pool);

    ensures pool->data[first->at] == 11;
} by {
    step(put(pool, first, 11), { r: a });
    step(put(pool, second, 22), { r: b });
    execute();
    simp();
}
```

```expect
pass
```
