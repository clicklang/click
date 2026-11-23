# a self-aliased field operand is one value

Bitcoin Core's `FeeFrac::operator-=` and `operator+=` read `this->size` and
`other.size`. Under `this == &other` both reads name one cell, so
`size - size` is 0 and is defined with no bounds, and `size + size` is
defined under bounds on `size` alone. The pointer equality is a fact about
the two pointers, not about their integer offsets; the overflow check reads
it to see that the second field read is the first one. The field is at a
nonzero offset, after `fee`, as in the original struct. The proof separates
the fee write's footprint from `size`, preserves the exact read, and uses the
pointer equality to identify the second operand. The companion
`a_self_aliased_field_sum_without_bounds_is_refused.md` shows the sum still
needs its bounds.

```c filename=a_self_aliased_field_operand_is_one_value.c
struct FeeFrac {
    int64 fee;
    int32 size;
};

void subtract_assign(struct FeeFrac* self, struct FeeFrac* other) {
    self->fee -= other->fee;
    self->size -= other->size;
}

void add_assign(struct FeeFrac* self, struct FeeFrac* other) {
    self->fee += other->fee;
    self->size += other->size;
}
```

```click
verifying "a_self_aliased_field_operand_is_one_value.c";

void subtract_assign(struct FeeFrac* self, struct FeeFrac* other) {
    requires self == other;
    owns self->fee;
    owns self->size;
    ensures self->fee == 0i64;
    ensures self->size == 0;
} by {
    apply(click::separation::separate_adjacent_ranges(self as (int32 *), 0, 2, 4));
    have contains(memory(self->size), memory((&self->size)[0..1])) by { normalize(); }
    apply(click::separation::contains_refl(memory(self->fee)));
    apply(click::separation::separate_restrict(memory(self->fee), memory(self->size),
        memory(self->fee), memory((&self->size)[0..1])));
    mark before_store;
    step();
    have separate(statement(0).footprint, memory((&self->size)[0..1])) by {
        normalize() using { at(before_store, separate(memory(self->fee), memory((&self->size)[0..1]))); };
    }
    have exact(self->size) == at(statement(0).entry, exact(self->size)) by {
        preserve(memory((&self->size)[0..1]), statement(0));
    }
    have other->size == old(self->size) by {
        rewrite(other, self);
        known();
    }
    step_until(function.exit);
    solve();
}

void add_assign(struct FeeFrac* self, struct FeeFrac* other) {
    requires self == other;
    owns self->fee;
    owns self->size;
    requires -4611686018427387904i64 <= self->fee;
    requires self->fee <= 4611686018427387903i64;
    requires -1073741824 <= self->size;
    requires self->size <= 1073741823;
    ensures to_integer(self->fee) == to_integer(old(self->fee) + old(self->fee));
    ensures to_integer(self->size) == to_integer(old(self->size) + old(self->size));
} by {
    apply(click::separation::separate_adjacent_ranges(self as (int32 *), 0, 2, 4));
    have contains(memory(self->size), memory((&self->size)[0..1])) by { normalize(); }
    apply(click::separation::contains_refl(memory(self->fee)));
    apply(click::separation::separate_restrict(memory(self->fee), memory(self->size),
        memory(self->fee), memory((&self->size)[0..1])));
    mark before_store;
    step();
    have separate(statement(0).footprint, memory((&self->size)[0..1])) by {
        normalize() using { at(before_store, separate(memory(self->fee), memory((&self->size)[0..1]))); };
    }
    have exact(self->size) == at(statement(0).entry, exact(self->size)) by {
        preserve(memory((&self->size)[0..1]), statement(0));
    }
    have other->size == old(self->size) by {
        rewrite(other, self);
        known();
    }
    step_until(function.exit);
    solve();
}
```

```expect
pass
```
