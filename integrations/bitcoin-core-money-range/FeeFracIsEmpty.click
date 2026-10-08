verifying "bitcoin-src/src/util/feefrac.h";

bool FeeFrac_IsEmpty(const struct FeeFrac* self) {
    views self->fee;
    views self->size;
    ensures self->fee == old(self->fee);
    ensures self->size == old(self->size);
    ensures result == (if old(self->size) == 0 { 1 } else { 0 });
    ensures result != 0 implies self->size == 0;
    ensures result == 0 implies self->size != 0;
} by {
    if self->size == 0 {
        execute();
        simp();
    } else {
        execute();
        simp();
    }
}
