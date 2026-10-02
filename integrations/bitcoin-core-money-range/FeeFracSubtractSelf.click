verifying "bitcoin-src/src/util/feefrac.h";

void FeeFrac_operator_subtract_assign(struct FeeFrac* self, const struct FeeFrac* other) {
    requires self == other;
    owns self->fee;
    owns self->size;
    ensures self->fee == 0i64;
    ensures self->size == 0;
} by {
    execute();
    simp();
}
