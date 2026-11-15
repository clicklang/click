import click::separation;
verifying "span-probe.cpp";

void FixtureReader::read(std::span<std::byte> dst) {
    requires std_span_size(dst) == 4u64;
    requires 4u64 <= this->remaining;
    requires separate(memory(std_span_data(dst)[0..4]), memory(this->data[0..4]));
    owns this->data;
    owns this->remaining;
    views this->data[0..4];
    consumes uninitialized(std_span_data(dst)[0..4]);
    produces std_span_data(dst)[0..4];
    ensures std_span_data(dst)[0] == old(this->data[0]);
    ensures std_span_data(dst)[1] == old(this->data[1]);
    ensures std_span_data(dst)[2] == old(this->data[2]);
    ensures std_span_data(dst)[3] == old(this->data[3]);
    ensures this->data == old(this->data) + 4;
    ensures this->remaining == old(this->remaining) - 4u64;
} by {
    have separate(memory(std_span_data(dst)[0..4]), memory(this->data)) by { solve(); }
    have contains(memory(this->data[0..4]), memory(this->data[0..4])) by {
        apply(click::separation::contains_refl(memory(this->data[0..4])));
    }
    have contains(memory(std_span_data(dst)[0..4]), memory(std_span_data(dst)[0])) by {
        apply(click::separation::contains_element(std_span_data(dst), 0, 4, 0)) using { 0 <= 0; 0 < 4; };
    }
    have separate(memory(std_span_data(dst)[0]), memory(this->data[0..4])) by {
        apply(click::separation::separate_restrict(memory(std_span_data(dst)[0..4]), memory(this->data[0..4]), memory(std_span_data(dst)[0]), memory(this->data[0..4]))) using {
            separate(memory(std_span_data(dst)[0..4]), memory(this->data[0..4]));
            contains(memory(std_span_data(dst)[0..4]), memory(std_span_data(dst)[0]));
            contains(memory(this->data[0..4]), memory(this->data[0..4]));
        };
    }
    have contains(memory(std_span_data(dst)[0..4]), memory(std_span_data(dst)[1])) by {
        apply(click::separation::contains_element(std_span_data(dst), 0, 4, 1)) using { 0 <= 1; 1 < 4; };
    }
    have separate(memory(std_span_data(dst)[1]), memory(this->data[0..4])) by {
        apply(click::separation::separate_restrict(memory(std_span_data(dst)[0..4]), memory(this->data[0..4]), memory(std_span_data(dst)[1]), memory(this->data[0..4]))) using {
            separate(memory(std_span_data(dst)[0..4]), memory(this->data[0..4]));
            contains(memory(std_span_data(dst)[0..4]), memory(std_span_data(dst)[1]));
            contains(memory(this->data[0..4]), memory(this->data[0..4]));
        };
    }
    have contains(memory(std_span_data(dst)[0..4]), memory(std_span_data(dst)[2])) by {
        apply(click::separation::contains_element(std_span_data(dst), 0, 4, 2)) using { 0 <= 2; 2 < 4; };
    }
    have separate(memory(std_span_data(dst)[2]), memory(this->data[0..4])) by {
        apply(click::separation::separate_restrict(memory(std_span_data(dst)[0..4]), memory(this->data[0..4]), memory(std_span_data(dst)[2]), memory(this->data[0..4]))) using {
            separate(memory(std_span_data(dst)[0..4]), memory(this->data[0..4]));
            contains(memory(std_span_data(dst)[0..4]), memory(std_span_data(dst)[2]));
            contains(memory(this->data[0..4]), memory(this->data[0..4]));
        };
    }
    have contains(memory(std_span_data(dst)[0..4]), memory(std_span_data(dst)[3])) by {
        apply(click::separation::contains_element(std_span_data(dst), 0, 4, 3)) using { 0 <= 3; 3 < 4; };
    }
    have separate(memory(std_span_data(dst)[3]), memory(this->data[0..4])) by {
        apply(click::separation::separate_restrict(memory(std_span_data(dst)[0..4]), memory(this->data[0..4]), memory(std_span_data(dst)[3]), memory(this->data[0..4]))) using {
            separate(memory(std_span_data(dst)[0..4]), memory(this->data[0..4]));
            contains(memory(std_span_data(dst)[0..4]), memory(std_span_data(dst)[3]));
            contains(memory(this->data[0..4]), memory(this->data[0..4]));
        };
    }
    step_until(call(0));
    step();
    have call(0).result == old(std_span_data(dst)) + 0 by { known(); }
    step();
    step() by { known(); }
    have this->data == old(this->data) by { solve(); }
    step_until(call(1));
    step();
    have call(1).result == old(std_span_data(dst)) + 1 by { known(); }
    step();
    step() by { known(); }
    have this->data == old(this->data) by { solve(); }
    step_until(call(2));
    step();
    have call(2).result == old(std_span_data(dst)) + 2 by { known(); }
    step();
    step() by { known(); }
    have this->data == old(this->data) by { solve(); }
    step_until(call(3));
    step();
    have call(3).result == old(std_span_data(dst)) + 3 by { known(); }
    step();
    step() by { known(); }
    have this->data == old(this->data) by { solve(); }
    step_until(function.exit);
    solve();
}

uint32 le32toh_internal(uint32 little_endian_32bits) {
    ensures result == little_endian_32bits;
}

uint32 ser_readdata32<FixtureReader>(struct FixtureReader& s) {
    requires 4u64 <= s.remaining;
    requires s.data[0] == 120u8;
    requires s.data[1] == 86u8;
    requires s.data[2] == 52u8;
    requires s.data[3] == 18u8;
    owns s.data;
    owns s.remaining;
    views s.data[0..4];
    ensures result == 305419896u32;
    ensures s.data == old(s.data) + 4;
    ensures s.remaining == old(s.remaining) - 4u64;
}

uint32 probe(struct FixtureReader& stream) {
    requires 4u64 <= stream.remaining;
    requires stream.data[0] == 120u8;
    requires stream.data[1] == 86u8;
    requires stream.data[2] == 52u8;
    requires stream.data[3] == 18u8;
    owns stream.data;
    owns stream.remaining;
    views stream.data[0..4];
    ensures result == 305419896u32;
    ensures stream.data == old(stream.data) + 4;
    ensures stream.remaining == old(stream.remaining) - 4u64;
}

