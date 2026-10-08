verifying "subtract_methods.cpp";

void FeeFrac_operator_subtract_assign(struct FeeFrac* this, const struct FeeFrac& other) {
    requires this == &other;
    owns this->fee;
    owns this->size;
    ensures this->fee == 0i64;
    ensures this->size == 0;
} by {
    execute();
    simp();
}

int32 clear_value(struct FeeFrac& value, int32& untouched) {
    owns value.fee;
    owns value.size;
    owns untouched;
    ensures value.fee == 0i64;
    ensures value.size == 0;
    ensures result == 0;
    ensures untouched == old(untouched);
} by {
    execute();
    simp();
}
