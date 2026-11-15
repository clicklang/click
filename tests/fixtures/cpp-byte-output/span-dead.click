verifying "span-probe.cpp";

void fill(std::span<std::byte> dst) {
    requires std_span_size(dst) == 4u64;
    consumes uninitialized(std_span_data(dst)[0..4]);
    produces std_span_data(dst)[0..4];
    ensures std_span_data(dst)[0] == 120u8;
    ensures std_span_data(dst)[1] == 86u8;
    ensures std_span_data(dst)[2] == 52u8;
    ensures std_span_data(dst)[3] == 18u8;
}

void expire(std::span<std::byte>& dst) {
    owns std_span_data(dst);
    owns std_span_size(dst);
    ensures std_span_size(dst) == 4u64;
}

uint32 probe() {
    ensures result == 0u32;
}
