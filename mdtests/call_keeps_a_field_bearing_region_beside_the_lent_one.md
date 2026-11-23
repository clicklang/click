# A call keeps a field-bearing region beside the lent one

`pool_slot` is a field-bearing region that owns its descriptor and
`pool->data[at..end]`. `two_puts` writes `11` through `first` and then
`22` through `second`, lending only `second`'s region to the second call,
and claims the first value survives. The caller keeps `first`'s region and
reloads `pool->data` to address its cell. The proof preserves the first
slot's index and cell across the second call, then uses `put`'s
`pool->data == old(pool->data)` to recover the original address.

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
import click::separation;
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
    step_until(function.exit);
    let r = fold(pool_slot(s, pool), { at: a, end: e });
    solve();
}

void two_puts(struct pool* pool, struct slot* first, struct slot* second) {
    owns pool->data;
    owns a: pool_slot(first, pool);
    owns b: pool_slot(second, pool);

    ensures pool->data[first->at] == 11;
} by {
    step(put, { r: a });
    have pool->data[first->at] == 11;
    let { at: first_at, end: first_end } = unfold(a);
    have separate(memory(pool->data), memory(*first)) by { known(); }
    have separate(b, memory(*first)) by { known(); }
    apply(separation::separate_star(memory(pool->data), b, memory(*first)));
    have contains(memory(*first), memory(first->at)) by { normalize(); }
    apply(separation::contains_refl(memory(pool->data) * b));
    apply(separation::separate_restrict(memory(pool->data) * b, memory(*first), memory(pool->data) * b, memory(first->at)));

    have separate(memory(pool->data), memory(pool->data[first_at..first_end])) by { known(); }
    have separate(b, memory(pool->data[first_at..first_end])) by { known(); }
    apply(separation::separate_star(memory(pool->data), b, memory(pool->data[first_at..first_end])));
    apply(separation::contains_element(pool->data, first_at, first_end, first_at));
    have contains(memory(pool->data[first_at]), memory(*(pool->data + first_at))) by { normalize(); }
    apply(separation::contains_trans(memory(pool->data[first_at..first_end]), memory(pool->data[first_at]), memory(*(pool->data + first_at))));
    apply(separation::separate_restrict(memory(pool->data) * b, memory(pool->data[first_at..first_end]), memory(pool->data) * b, memory(*(pool->data + first_at))));
    have pool->data[first_at] == 11 by { known(); }
    mark before_second_put;
    step(put, { r: b });
    have contains(memory(pool->data) * at(before_second_put, b), statement(1).footprint) by { known(); }
    apply(separation::contains_refl(memory(first->at)));
    apply(separation::separate_restrict(
        memory(pool->data) * at(before_second_put, b), memory(first->at),
        statement(1).footprint, memory(first->at)));
    have first->at == at(before_second_put, first->at) by {
        preserve(memory(first->at), statement(1));
    }
    have pool->data == at(before_second_put, pool->data);
    apply(separation::contains_refl(memory(at(before_second_put, pool->data + first_at)[0])));
    apply(separation::separate_restrict(
        memory(pool->data) * at(before_second_put, b), memory(at(before_second_put, pool->data + first_at)[0]),
        statement(1).footprint, memory(at(before_second_put, pool->data + first_at)[0])));
    have (let saved: int32* = at(before_second_put, pool->data + first_at); saved[0])
        == at(before_second_put, pool->data[first_at]) by {
        preserve(memory(at(before_second_put, pool->data + first_at)[0]), statement(1));
    }
    have first->at == first_at by { known(); }
    have pool->data[first->at] == 11 by {
        rewrite(first->at, first_at);
        rewrite(pool->data, at(before_second_put, pool->data));
        known();
    }
    let a = fold(pool_slot(first, pool), { at: first_at, end: first_end });
}
```

```expect
pass
```
