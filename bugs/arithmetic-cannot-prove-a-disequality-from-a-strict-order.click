theorem native_lt_neq(k: int32, j: int32) {
    requires k < j;
    ensures k != j by auto();
}
theorem integer_lt_neq(k: Integer, j: Integer) {
    requires k < j;
    ensures k != j by auto();
}
theorem integer_lt_neq_arithmetic(k: Integer, j: Integer) {
    requires k < j;
    ensures k != j by { arithmetic() using { k < j; }; }
}
theorem native_lt_neq_arithmetic(k: int32, j: int32) {
    requires k < j;
    ensures k != j by { arithmetic() using { k < j; }; }
}
