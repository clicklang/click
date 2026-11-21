# A frame holds across a write at a 64-bit index

`set_at` writes one element through a pointer `at` returned, and its
contract says every other element is unchanged. The size is a field of
a nested struct, as `std::span` keeps it.

The store's footprint is separate from the array pointer and length fields,
so the proof preserves both fields across the store. For each `k != i`, the
proof uses separation of the two indexed cells and preserves the exact
element address saved at the store's entry. The argument uses the full
64-bit indices.

`a_frame_over_a_64_bit_indexed_write_must_exclude_its_cell.md` is a smaller
store whose frame drops `k != i` and is refused.

```c filename=a_frame_holds_across_a_write_at_a_64_bit_index.c
struct E { unsigned long v; };
struct S { int *p; struct E e; };
int *at(const struct S *s, unsigned long i) { return s->p + i; }
int set_at(struct S *s, unsigned long i, int v) { int *e = at(s, i); *e = v; return *e; }
```

```click
import click::separation;
verifying "a_frame_holds_across_a_write_at_a_64_bit_index.c";
int32* at(const struct S* s, uint64 i) {
    views s->p;
    views s->e.v;
    views s->p[0..s->e.v];
    requires i < s->e.v;
    ensures result == s->p + i;
}
int32 set_at(struct S* s, uint64 i, int32 v) {
    views s->p;
    views s->e.v;
    owns s->p[0..s->e.v];
    requires i < s->e.v;
    ensures result == v;
    ensures s->p[i] == v;
    ensures forall (k: uint64) { k < s->e.v and k != i implies s->p[k] == old(s->p[k]) };
} by {
    step_until(statement(1).entry);
    have s->p == old(s->p) by { solve(); }
    have s->e.v == old(s->e.v) by { solve(); }
    have e == s->p + i by { known(); }
    step();
    have separate(memory(*e), memory(s->p) * memory(s->e.v)) by { known(); }
    apply(separation::contains_left(memory(s->p), memory(s->e.v))) using {};
    apply(separation::contains_refl(memory(*e))) using {};
    apply(separation::separate_restrict(
        memory(*e), memory(s->p) * memory(s->e.v), memory(*e), memory(s->p)
    )) using {
        separate(memory(*e), memory(s->p) * memory(s->e.v));
        contains(memory(*e), memory(*e));
        contains(memory(s->p) * memory(s->e.v), memory(s->p));
    };
    have separate(statement(1).footprint, memory(s->p)) by {
        known();
    }
    have s->p == at(statement(1).entry, s->p) by {
        preserve(memory(s->p), statement(1));
    }
    have s->p == old(s->p) by {
        rewrite(s->p, at(statement(1).entry, s->p));
        known();
    }
    apply(separation::contains_right(memory(s->p), memory(s->e.v))) using {};
    apply(separation::separate_restrict(
        memory(*e), memory(s->p) * memory(s->e.v), memory(*e), memory(s->e.v)
    )) using {
        separate(memory(*e), memory(s->p) * memory(s->e.v));
        contains(memory(*e), memory(*e));
        contains(memory(s->p) * memory(s->e.v), memory(s->e.v));
    };
    have separate(statement(1).footprint, memory(s->e.v)) by {
        known();
    }
    have s->e.v == at(statement(1).entry, s->e.v) by {
        preserve(memory(s->e.v), statement(1));
    }
    have s->e.v == old(s->e.v) by {
        rewrite(s->e.v, at(statement(1).entry, s->e.v));
        known();
    }
    have forall (k: uint64) { k < s->e.v and k != i implies s->p[k] == old(s->p[k]) } by {
        intro(); intro();
        apply(separation::separate_elements(s->p, i, k)) using { k != i; };
        have separate(memory(*e), memory(at(statement(1).entry, s->p + k)[0])) by {
            rewrite(e, s->p + i);
            rewrite(at(statement(1).entry, s->p), s->p);
            known();
        }
        have separate(statement(1).footprint, memory(at(statement(1).entry, s->p + k)[0])) by {
            known();
        }
        have (let saved: int32* = at(statement(1).entry, s->p + k); saved[0]) ==
            at(statement(1).entry, s->p[k]) by {
            preserve(memory(at(statement(1).entry, s->p + k)[0]), statement(1));
        }
        have at(statement(1).entry, s->p[k]) == old(s->p[k]) by { known(); }
        rewrite(s->p, at(statement(1).entry, s->p));
        known();
    }
    step();
    solve();
}
```

```expect
pass
```
