# Explicit separation preserves a kept slot cell across a call

`two_puts` writes `11` through `first`, then lends the pool and `second`
to another `put`. The proof opens the retained slot, restricts the call's
resource footprint to its index and data cell, and uses ordinary `preserve`
steps. The callee's pointer equality relates the two base spellings.
A local expression binding reads current memory through the saved pointer;
indexing the historical array reference itself would read historical memory.

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
import click::separation;
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
    have to_integer(a + 1) <= to_integer(e);
    have s->at == a by {
        assumption();
    }
    have to_integer(s->at + 1) <= to_integer(e) by {
        rewrite(s->at == a);
        assumption();
    }
    step_until(function.exit);
    let r = fold(pool_slot(s, pool), { at: a, end: e });
    solve();
}

void two_puts(struct pool* pool, struct slot* first, struct slot* second) {
    owns *pool;
    owns a: pool_slot(first, pool);
    owns b: pool_slot(second, pool);
    ensures pool->data[first->at] == 11;
} by {
    step(put, { r: a });
    have pool->data[first->at] == 11;
    let { at: first_at, end: first_end } = unfold(a);
    have separate(memory(*pool), memory(*first)) by { assumption(); }
    have separate(b, memory(*first)) by { assumption(); }
    apply(separation::separate_star(memory(*pool), b, memory(*first)));
    have contains(memory(*first), memory(first->at)) by { normalize(); }
    apply(separation::contains_refl(memory(*pool) * b));
    apply(separation::separate_restrict(memory(*pool) * b, memory(*first), memory(*pool) * b, memory(first->at)));

    have separate(memory(*pool), memory(pool->data[first_at..first_end])) by { assumption(); }
    have separate(b, memory(pool->data[first_at..first_end])) by { assumption(); }
    apply(separation::separate_star(memory(*pool), b, memory(pool->data[first_at..first_end])));
    apply(separation::contains_element(pool->data, first_at, first_end, first_at));
    have contains(memory(pool->data[first_at]), memory(*(pool->data + first_at))) by { normalize(); }
    apply(separation::contains_trans(memory(pool->data[first_at..first_end]), memory(pool->data[first_at]), memory(*(pool->data + first_at))));
    apply(separation::separate_restrict(memory(*pool) * b, memory(pool->data[first_at..first_end]), memory(*pool) * b, memory(*(pool->data + first_at))));
    have pool->data[first_at] == 11 by { assumption(); }
    mark m1;
    step(put, { r: b });
    have contains(memory(*pool) * at(m1, b), statement(1).footprint) by { assumption(); }
    apply(separation::contains_refl(memory(first->at)));
    apply(separation::separate_restrict(memory(*pool) * at(m1, b), memory(first->at), statement(1).footprint, memory(first->at))) using {
        at(m1, separate(memory(*pool) * b, memory(first->at)));
        contains(memory(*pool) * at(m1, b), statement(1).footprint);
        contains(memory(first->at), memory(first->at));
    };
    have first->at == at(m1, first->at) by {
        preserve(separate(statement(1).footprint, memory(first->at)));
    }
    have pool->data == at(m1, pool->data);
    apply(separation::contains_refl(memory(at(m1, pool->data + first_at)[0])));
    apply(separation::separate_restrict(memory(*pool) * at(m1, b), memory(at(m1, pool->data + first_at)[0]), statement(1).footprint, memory(at(m1, pool->data + first_at)[0]))) using {
        at(m1, separate(memory(*pool) * b, memory(*(pool->data + first_at))));
        contains(memory(*pool) * at(m1, b), statement(1).footprint);
        contains(memory(at(m1, pool->data + first_at)[0]), memory(at(m1, pool->data + first_at)[0]));
    };
    have (let saved: int32* = at(m1, pool->data + first_at); saved[0]) == at(m1, pool->data[first_at]) by {
        preserve(separate(statement(1).footprint, memory(at(m1, pool->data + first_at)[0])));
    }
    have first->at == first_at by { assumption(); }
    have pool->data[first->at] == 11 by {
        rewrite(first->at == first_at);
        rewrite(pool->data == at(m1, pool->data));
        assumption();
    }
    let a = fold(pool_slot(first, pool), { at: first_at, end: first_end });
}
```

```expect
pass
```
