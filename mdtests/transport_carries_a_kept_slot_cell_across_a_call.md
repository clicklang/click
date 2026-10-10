# Transport carries a kept slot cell across a call

`two_puts` writes `11` through the slot `first`, then lends the pool and the
slot `second` to a second `put`, and still claims the first cell holds `11`.
The cell is `pool->data[first->at]`, indexed by a load from the kept slot,
and `pool->data` is reloaded after the call. `transport` carries the value
across the call: the call's havoc is separated from the kept slot's range,
and `put`'s `pool->data == old(pool->data)` relates the two spellings of the
base. Proving the index loads equal at the two states falls through to the
memory-resolution order rule, so this catches that rule refusing the two
loads of `first->at` that the kept slot leaves unchanged. It is the reduced
form of `call_keeps_region_beside_folded_arena_state.md`, without the folded
arena state.

```c filename=transport_carries_a_kept_slot_cell_across_a_call.c
struct pool {
    int32* data;
};

struct slot {
    int32 at;
    int32 end;
};

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
    fact 0 <= at;
    fact at < end;
}

verifying "transport_carries_a_kept_slot_cell_across_a_call.c";

void put(struct pool* pool, struct slot* s, int32 value) {
    owns *pool;
    owns r: pool_slot(s, pool);
    ensures r.at == old(r.at);
    ensures r.end == old(r.end);
    ensures pool->data == old(pool->data);
    ensures pool->data[s->at] == value;
} by {
    let { at: a, end: e } = unfold(r);
    have a + 1 <= e by {
        apply(int32_increment_upper_bound(a, e)) using {
            a < e;
        }
    }
    have s->at == a by {
        assumption();
    }
    have s->at + 1 <= e by {
        rewrite(s->at == a);
        assumption();
    }
    execute();
    let r = fold(pool_slot(s, pool), { at: a, end: e });
    simp();
}

void two_puts(struct pool* pool, struct slot* first, struct slot* second) {
    owns *pool;
    owns a: pool_slot(first, pool);
    owns b: pool_slot(second, pool);
    ensures pool->data[first->at] == 11;
} by {
    step(put(pool, first, 11), { r: a });
    have pool->data[first->at] == 11;
    mark m1;
    step(put(pool, second, 22), { r: b });
    have pool->data == at(m1, pool->data);
    have pool->data[first->at] == 11 by {
        transport(at(m1, pool->data[first->at]) == 11, pool->data[first->at] == 11) using {
            at(m1, pool->data[first->at]) == 11;
            pool->data == at(m1, pool->data);
        }
    }
    execute();
    simp();
}
```

```expect
pass
```
