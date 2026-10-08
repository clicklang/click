verifying "value_methods.cpp";

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

int32 double_size(struct FeeFrac& value, int32& untouched) {
    owns untouched;
    ensures untouched == old(untouched);
    owns value.fee;
    owns value.size;
    requires -4611686018427387904 <= value.fee;
    requires value.fee <= 4611686018427387903;
    requires -1073741824 <= value.size;
    requires value.size <= 1073741823;
    ensures value.fee == old(value.fee) + old(value.fee);
    ensures value.size == old(value.size) + old(value.size);
    ensures result == value.size;
} by {
    execute();
    simp();
}
