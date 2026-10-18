theorem int32_less_equal_to_integer(left: int32, right: int32) {
    requires left <= right;
    ensures left <= right by assumption();
}
