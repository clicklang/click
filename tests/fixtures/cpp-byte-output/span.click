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

uint32 probe() {
    ensures result == 305419896u32;
} by {
    step_until(call(fill, 0));
    have std_span_size(dst) == 4u64 by { solve(); }
    step();
    have std_span_data(dst) == ((&obj) as (uint8*)) by { known(); }
    have ((&obj) as (uint8*))[0] == 120u8 by { solve(); }
    have ((&obj) as (uint8*))[1] == 86u8 by { solve(); }
    have ((&obj) as (uint8*))[2] == 52u8 by { solve(); }
    have ((&obj) as (uint8*))[3] == 18u8 by { solve(); }
    step_until(function.exit);
    solve();
}
