// Prove cast identities on scalar arguments and apply them to the caller's
// fields and expressions after establishing their bounds.
theorem fee_to_uint64(value: int64) {
    requires 0 <= to_integer(value);
    requires to_integer(value) <= 8589934591;
    ensures to_integer(value as uint64) == to_integer(value) by {
        close() using { 0 <= to_integer(value); to_integer(value) <= 8589934591; };
    }
}
theorem amount_to_uint64(value: int32) {
    requires 0 <= to_integer(value);
    requires to_integer(value) <= 2147483647;
    ensures to_integer(value as uint64) == to_integer(value) by {
        close() using { 0 <= to_integer(value); to_integer(value) <= 2147483647; };
    }
}
theorem size_to_uint32(value: int32) {
    requires 1 <= to_integer(value);
    requires to_integer(value) <= 2147483647;
    ensures to_integer(value as uint32) == to_integer(value) by {
        close() using { 1 <= to_integer(value); to_integer(value) <= 2147483647; };
    }
}
theorem size_to_uint64(value: uint32) {
    requires 0 <= to_integer(value);
    requires to_integer(value) <= 4294967295;
    ensures to_integer(value as uint64) == to_integer(value) by {
        close() using { 0 <= to_integer(value); to_integer(value) <= 4294967295; };
    }
}
theorem fee_result_to_int64(value: uint64) {
    requires 0 <= to_integer(value);
    requires to_integer(value) <= 9223372036854775807;
    ensures to_integer(value as int64) == to_integer(value) by {
        close() using { 0 <= to_integer(value); to_integer(value) <= 9223372036854775807; };
    }
}
