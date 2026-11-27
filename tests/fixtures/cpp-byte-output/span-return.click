verifying "span-probe.cpp";
std::span<std::byte> probe(std::span<int> span) {
    ensures std_span_data(result) == old(std_span_data(span) as (uint8 *));
    ensures std_span_size(result) == old(std_span_size(span)) * 4u64;
} by {
    step_until(call(0).entry);
    step();
    mark before_return;
    have std_span_data(call(0).parameter(__sp)) == old(std_span_data(span)) by { close(); }
    have std_span_size(call(0).parameter(__sp)) == old(std_span_size(span)) by { close(); }
    have std_span_size(call(0).result) == std_span_size(call(0).parameter(__sp)) * 4u64 by { close(); }
    have std_span_data(call(0).result) == old(std_span_data(span) as (uint8 *)) by { close(); }
    have separate(memory(at(call(0).exit, call(0).result)[0..8]), memory(at(before_return, span)[0])) by { close(); }
    have separate(memory(at(call(0).exit, call(0).result)[8..16]), memory(at(before_return, span)[0])) by { close(); }
    // The copied argument is the storage reserved at region(0).
    have separate(memory(at(call(0).exit, call(0).result)[0..8]),
                  memory(at(region(0).exit, region(0).result)[0..16])) by close();
    have separate(memory(at(call(0).exit, call(0).result)[8..16]),
                  memory(at(region(0).exit, region(0).result)[0..16])) by close();
    step_until(function.exit);
    // Carry each result field across the copied argument and parameter retirements.
    have separate(region(3).footprint, memory(at(call(0).exit, call(0).result)[0..8])) by {
        close() using { separate(memory(at(call(0).exit, call(0).result)[0..8]), memory(at(region(0).exit, region(0).result)[0..16])); };
    }
    have at(region(3).exit, load<uint8*>(call(0).result)) ==
         at(region(3).entry, load<uint8*>(call(0).result)) by {
        preserve(memory(at(call(0).exit, call(0).result)[0..8]), region(3));
    }
    have separate(region(4).footprint, memory(at(call(0).exit, call(0).result)[0..8])) by {
        close() using { separate(memory(at(call(0).exit, call(0).result)[0..8]), memory(at(before_return, span)[0])); };
    }
    have std_span_data(result) == at(region(4).entry, load<uint8*>(call(0).result)) by {
        preserve(memory(at(call(0).exit, call(0).result)[0..8]), region(4));
    }
    have std_span_data(result) == std_span_data(call(0).result) by {
        rewrite(std_span_data(result), at(region(4).entry, load<uint8*>(call(0).result)));
        close();
    }
    have separate(region(3).footprint, memory(at(call(0).exit, call(0).result)[8..16])) by {
        close() using { separate(memory(at(call(0).exit, call(0).result)[8..16]), memory(at(region(0).exit, region(0).result)[0..16])); };
    }
    have at(region(3).exit, load<uint64>(byte_offset(call(0).result, 8))) ==
         at(region(3).entry, load<uint64>(byte_offset(call(0).result, 8))) by {
        preserve(memory(at(call(0).exit, call(0).result)[8..16]), region(3));
    }
    have separate(region(4).footprint, memory(at(call(0).exit, call(0).result)[8..16])) by {
        close() using { separate(memory(at(call(0).exit, call(0).result)[8..16]), memory(at(before_return, span)[0])); };
    }
    have std_span_size(result) == at(region(4).entry, load<uint64>(byte_offset(call(0).result, 8))) by {
        preserve(memory(at(call(0).exit, call(0).result)[8..16]), region(4));
    }
    have std_span_size(result) == std_span_size(call(0).result) by {
        rewrite(std_span_size(result), at(region(4).entry, load<uint64>(byte_offset(call(0).result, 8))));
        close();
    }
    close();
}
