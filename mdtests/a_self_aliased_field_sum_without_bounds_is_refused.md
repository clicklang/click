# a self-aliased field sum without bounds is refused

The companion of `a_self_aliased_field_operand_is_one_value.md`: under
`this == &other`, `this->size + other.size` is `size + size`, which
overflows for a large `size`. Knowing that the two reads are one value does
not make the sum defined; without bounds on `size` it is refused.

```c filename=a_self_aliased_field_sum_without_bounds_is_refused.c
struct FeeFrac {
    int64 fee;
    int32 size;
};

void add_assign(struct FeeFrac* self, struct FeeFrac* other) {
    self->size += other->size;
}
```

```click
verifying "a_self_aliased_field_sum_without_bounds_is_refused.c";

void add_assign(struct FeeFrac* self, struct FeeFrac* other) {
    requires self == other;
    owns self->size;
    ensures self->size == old(self->size) + old(self->size);
} by {
    execute();
    simp();
}
```

```expect
fail: signed overflow
```
