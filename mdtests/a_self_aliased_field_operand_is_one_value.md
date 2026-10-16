# a self-aliased field operand is one value

Bitcoin Core's `FeeFrac::operator-=` and `operator+=` read `this->size` and
`other.size`. Under `this == &other` both reads name one cell, so
`size - size` is 0 and is defined with no bounds, and `size + size` is
defined under bounds on `size` alone. The pointer equality is a fact about
the two pointers, not about their integer offsets; the overflow check reads
it to see that the second field read is the first one. The field is at a
nonzero offset, after `fee`, as in the original struct. The companion
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
    execute();
    simp();
}

void add_assign(struct FeeFrac* self, struct FeeFrac* other) {
    requires self == other;
    owns self->fee;
    owns self->size;
    requires -4611686018427387904i64 <= self->fee;
    requires self->fee <= 4611686018427387903i64;
    requires -1073741824 <= self->size;
    requires self->size <= 1073741823;
    ensures self->fee == old(self->fee) + old(self->fee);
    ensures self->size == old(self->size) + old(self->size);
} by {
    execute();
    simp();
}
```

```expect
pass
```
