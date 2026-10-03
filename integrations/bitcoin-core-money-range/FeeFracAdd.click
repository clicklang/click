verifying "bitcoin-src/src/util/feefrac.h";

void FeeFrac_operator_add_assign(struct FeeFrac* self, const struct FeeFrac* other) {
    owns self->fee;
    owns self->size;
    owns other->fee;
    owns other->size;
    requires -4611686018427387904 <= self->fee;
    requires self->fee <= 4611686018427387903;
    requires -4611686018427387904 <= other->fee;
    requires other->fee <= 4611686018427387903;
    requires -1073741824 <= self->size;
    requires self->size <= 1073741823;
    requires -1073741824 <= other->size;
    requires other->size <= 1073741823;
    ensures self->fee == old(self->fee) + old(other->fee);
    ensures self->size == old(self->size) + old(other->size);
    ensures other->fee == old(other->fee);
    ensures other->size == old(other->size);
} by {
    execute();
    simp();
}
