verifying "span-probe.cpp";

uint64 length(std::span<std::byte> view) {
    requires std_span_size(view) == 4u64;
    ensures result == 4u64;
}

uint32 probe() {
    ensures result == 4u32;
} by {
    step_until(call(length, 0));
    have std_span_size(dst) == 4u64 by { known(); }
    step() by { known(); }
}
