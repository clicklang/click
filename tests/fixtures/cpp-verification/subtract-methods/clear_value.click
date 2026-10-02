verifying "subtract_methods.cpp";

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

int32 clear_value(struct FeeFrac* value, int32* untouched) {
    owns value->fee;
    owns value->size;
    owns untouched[0..1];
    ensures value->fee == 0i64;
    ensures value->size == 0;
    ensures result == 0;
    ensures untouched[0] == old(untouched[0]);
} by {
    execute();
    simp();
}
