verifying "span-probe.cpp";

std::span<std::byte> probe(const std::span<int>& span) {
    views std_span_data(span);
    views std_span_size(span);
    ensures std_span_data(result) == std_span_data(span) as (uint8 *);
    ensures std_span_size(result) == std_span_size(span) * 4u64;
    ensures std_span_data(span) == old(std_span_data(span));
    ensures std_span_size(span) == old(std_span_size(span));
} by {
    step_until(call(0).entry);
    step();
    have std_span_data(call(0).parameter(__sp)) == old(std_span_data(span)) by close();
    have std_span_size(call(0).parameter(__sp)) == old(std_span_size(span)) by close();
    have std_span_data(call(0).result) == old(std_span_data(span) as (uint8 *)) by close();
    have std_span_size(call(0).result) == old(std_span_size(span)) * 4u64 by close();
    have separate(memory(at(call(0).exit, call(0).result)[0..8]),
                  memory(at(region(0).exit, region(0).result)[0..16])) by close();
    have separate(memory(at(call(0).exit, call(0).result)[8..16]),
                  memory(at(region(0).exit, region(0).result)[0..16])) by close();
    step_until(function.exit);
    have separate(region(3).footprint, memory(at(call(0).exit, call(0).result)[0..8])) by {
        close() using { separate(memory(at(call(0).exit, call(0).result)[0..8]), memory(at(region(0).exit, region(0).result)[0..16])); };
    }
    have std_span_data(result) == at(region(3).entry, load<uint8*>(call(0).result)) by {
        preserve(memory(at(call(0).exit, call(0).result)[0..8]), region(3));
    }
    have separate(region(3).footprint, memory(at(call(0).exit, call(0).result)[8..16])) by {
        close() using { separate(memory(at(call(0).exit, call(0).result)[8..16]), memory(at(region(0).exit, region(0).result)[0..16])); };
    }
    have std_span_size(result) == at(region(3).entry, load<uint64>(byte_offset(call(0).result, 8))) by {
        preserve(memory(at(call(0).exit, call(0).result)[8..16]), region(3));
    }
    close();
}
