verifying "bitcoin-src/src/util/feefrac.h";

void FeeFrac_operator_add_assign(struct FeeFrac* self, const struct FeeFrac& other) {
    requires self == &other;
    owns self->fee;
    owns self->size;
    requires -4611686018427387904 <= self->fee;
    requires self->fee <= 4611686018427387903;
    requires -1073741824 <= self->size;
    requires self->size <= 1073741823;
    ensures self->fee == old(self->fee) + old(self->fee);
    ensures self->size == old(self->size) + old(self->size);
} by {
    execute();
    simp();
}
