theorem int32_add_to_integer(left: int32, right: int32) {
    requires defined(left + right);
    ensures left == left by simp();
}
