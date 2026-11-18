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
    have separate(memory(dst->_M_ptr[0..4]), memory(this->data)) by {
        known();
    }
    have contains(memory(this->data[0..4]), memory(this->data[0..4])) by {
        apply(click::separation::contains_refl(memory(this->data[0..4]))) using {
        };
    }
    have contains(memory(dst->_M_ptr[0..4]), memory(dst->_M_ptr[0])) by {
        apply(click::separation::contains_element(dst->_M_ptr, 0, 4, 0)) using {
            0 <= 0;
            0 < 4;
        };
    }
    have separate(memory(dst->_M_ptr[0]), memory(this->data[0..4])) by {
        apply(click::separation::separate_restrict(memory(dst->_M_ptr[0..4]), memory(this->data[0..4]), memory(dst->_M_ptr[0]), memory(this->data[0..4]))) using {
            separate(memory(dst->_M_ptr[0..4]), memory(this->data[0..4]));
            contains(memory(dst->_M_ptr[0..4]), memory(dst->_M_ptr[0]));
            contains(memory(this->data[0..4]), memory(this->data[0..4]));
        };
    }
    have contains(memory(dst->_M_ptr[0..4]), memory(dst->_M_ptr[1])) by {
        apply(click::separation::contains_element(dst->_M_ptr, 0, 4, 1)) using {
            0 <= 1;
            1 < 4;
        };
    }
    have separate(memory(dst->_M_ptr[1]), memory(this->data[0..4])) by {
        apply(click::separation::separate_restrict(memory(dst->_M_ptr[0..4]), memory(this->data[0..4]), memory(dst->_M_ptr[1]), memory(this->data[0..4]))) using {
            separate(memory(dst->_M_ptr[0..4]), memory(this->data[0..4]));
            contains(memory(dst->_M_ptr[0..4]), memory(dst->_M_ptr[1]));
            contains(memory(this->data[0..4]), memory(this->data[0..4]));
        };
    }
    have contains(memory(dst->_M_ptr[0..4]), memory(dst->_M_ptr[2])) by {
        apply(click::separation::contains_element(dst->_M_ptr, 0, 4, 2)) using {
            0 <= 2;
            2 < 4;
        };
    }
    have separate(memory(dst->_M_ptr[2]), memory(this->data[0..4])) by {
        apply(click::separation::separate_restrict(memory(dst->_M_ptr[0..4]), memory(this->data[0..4]), memory(dst->_M_ptr[2]), memory(this->data[0..4]))) using {
            separate(memory(dst->_M_ptr[0..4]), memory(this->data[0..4]));
            contains(memory(dst->_M_ptr[0..4]), memory(dst->_M_ptr[2]));
            contains(memory(this->data[0..4]), memory(this->data[0..4]));
        };
    }
    have contains(memory(dst->_M_ptr[0..4]), memory(dst->_M_ptr[3])) by {
        apply(click::separation::contains_element(dst->_M_ptr, 0, 4, 3)) using {
            0 <= 3;
            3 < 4;
        };
    }
    have separate(memory(dst->_M_ptr[3]), memory(this->data[0..4])) by {
        apply(click::separation::separate_restrict(memory(dst->_M_ptr[0..4]), memory(this->data[0..4]), memory(dst->_M_ptr[3]), memory(this->data[0..4]))) using {
            separate(memory(dst->_M_ptr[0..4]), memory(this->data[0..4]));
            contains(memory(dst->_M_ptr[0..4]), memory(dst->_M_ptr[3]));
            contains(memory(this->data[0..4]), memory(this->data[0..4]));
        };
    }
    step();
    step();
    step();
    step() by {
        have at(function.entry, 0u64) < at(function.entry, load_uint64(byte_offset(dst, 8))) by {
            rewrite(at(region(3).entry, at(region(1).exit, dst->_M_extent._M_extent_value)), at(region(3).entry, 4u64));
            known();
        }
        known();
    }
    have call(0).result == (old(dst->_M_ptr) + 0) by {
        known();
    }
    step();
    step() by {
        known();
    }
    have separate(memory(at(call(0).exit, call(0).result)[0]), memory(this->data)) by {
        known();
    }
    have separate(region(5).footprint, memory(this->data)) by {
        normalize() using {
            separate(memory(at(call(0).exit, call(0).result)[0]), memory(this->data));
        };
    }
    have at(region(5).exit, this->data) == at(region(5).entry, this->data) by {
        preserve(memory(this->data), region(5));
    }
    have this->data == old(this->data) by {
        known();
    }
    have separate(memory(at(call(0).exit, call(0).result)[0]), memory(this->remaining)) by {
        known();
    }
    have separate(region(5).footprint, memory(this->remaining)) by {
        normalize() using {
            separate(memory(at(call(0).exit, call(0).result)[0]), memory(this->remaining));
        };
    }
    have at(region(5).exit, this->remaining) == at(region(5).entry, this->remaining) by {
        preserve(memory(this->remaining), region(5));
    }
    have this->remaining == old(this->remaining) by {
        known();
    }
    have separate(memory(at(call(0).exit, call(0).result)[0]), memory(old(this->data)[0])) by {
        transport(at(function.entry, separate(memory(at(call(0).exit, call(0).result)[0]), memory(old(this->data)[0]))), separate(memory(at(call(0).exit, call(0).result)[0]), memory(old(this->data)[0]))) using {
        };
    }
    have separate(region(5).footprint, memory(old(this->data)[0])) by {
        normalize() using {
            separate(memory(at(call(0).exit, call(0).result)[0]), memory(old(this->data)[0]));
        };
    }
    have at(region(5).exit, load_uint8((old(this->data) + 0))) == at(region(5).entry, load_uint8((old(this->data) + 0))) by {
        preserve(memory(old(this->data)[0]), region(5));
    }
    have load_uint8((old(this->data) + 0)) == old(this->data[0]) by {
        known();
    }
    have load_uint8((old(dst->_M_ptr) + 0)) == old(this->data[0]) by {
        known();
    }
    have separate(memory(at(call(0).exit, call(0).result)[0]), memory(old(this->data)[1])) by {
        transport(at(function.entry, separate(memory(at(call(0).exit, call(0).result)[0]), memory(old(this->data)[1]))), separate(memory(at(call(0).exit, call(0).result)[0]), memory(old(this->data)[1]))) using {
        };
    }
    have separate(region(5).footprint, memory(old(this->data)[1])) by {
        normalize() using {
            separate(memory(at(call(0).exit, call(0).result)[0]), memory(old(this->data)[1]));
        };
    }
    have at(region(5).exit, load_uint8((old(this->data) + 1))) == at(region(5).entry, load_uint8((old(this->data) + 1))) by {
        preserve(memory(old(this->data)[1]), region(5));
    }
    have load_uint8((old(this->data) + 1)) == old(this->data[1]) by {
        known();
    }
    have separate(memory(at(call(0).exit, call(0).result)[0]), memory(old(this->data)[2])) by {
        transport(at(function.entry, separate(memory(at(call(0).exit, call(0).result)[0]), memory(old(this->data)[2]))), separate(memory(at(call(0).exit, call(0).result)[0]), memory(old(this->data)[2]))) using {
        };
    }
    have separate(region(5).footprint, memory(old(this->data)[2])) by {
        normalize() using {
            separate(memory(at(call(0).exit, call(0).result)[0]), memory(old(this->data)[2]));
        };
    }
    have at(region(5).exit, load_uint8((old(this->data) + 2))) == at(region(5).entry, load_uint8((old(this->data) + 2))) by {
        preserve(memory(old(this->data)[2]), region(5));
    }
    have load_uint8((old(this->data) + 2)) == old(this->data[2]) by {
        known();
    }
    have separate(memory(at(call(0).exit, call(0).result)[0]), memory(old(this->data)[3])) by {
        transport(at(function.entry, separate(memory(at(call(0).exit, call(0).result)[0]), memory(old(this->data)[3]))), separate(memory(at(call(0).exit, call(0).result)[0]), memory(old(this->data)[3]))) using {
        };
    }
    have separate(region(5).footprint, memory(old(this->data)[3])) by {
        normalize() using {
            separate(memory(at(call(0).exit, call(0).result)[0]), memory(old(this->data)[3]));
        };
    }
    have at(region(5).exit, load_uint8((old(this->data) + 3))) == at(region(5).entry, load_uint8((old(this->data) + 3))) by {
        preserve(memory(old(this->data)[3]), region(5));
    }
    have load_uint8((old(this->data) + 3)) == old(this->data[3]) by {
        known();
    }
    step();
    step();
    step();
    step() by {
        have at(function.entry, 1u64) < at(function.entry, load_uint64(byte_offset(dst, 8))) by {
            rewrite(at(region(9).entry, at(region(7).exit, dst->_M_extent._M_extent_value)), at(region(9).entry, 4u64));
            known();
        }
        known();
    }
    have call(1).result == (old(dst->_M_ptr) + 1) by {
        known();
    }
    step();
    step() by {
        known();
    }
    have separate(memory(at(call(1).exit, call(1).result)[0]), memory(this->data)) by {
        known();
    }
    have separate(region(11).footprint, memory(this->data)) by {
        normalize() using {
            separate(memory(at(call(1).exit, call(1).result)[0]), memory(this->data));
        };
    }
    have at(region(11).exit, this->data) == at(region(11).entry, this->data) by {
        preserve(memory(this->data), region(11));
    }
    have this->data == old(this->data) by {
        known();
    }
    have separate(memory(at(call(1).exit, call(1).result)[0]), memory(this->remaining)) by {
        known();
    }
    have separate(region(11).footprint, memory(this->remaining)) by {
        normalize() using {
            separate(memory(at(call(1).exit, call(1).result)[0]), memory(this->remaining));
        };
    }
    have at(region(11).exit, this->remaining) == at(region(11).entry, this->remaining) by {
        preserve(memory(this->remaining), region(11));
    }
    have this->remaining == old(this->remaining) by {
        known();
    }
    have separate(memory(at(call(1).exit, call(1).result)[0]), memory(old(this->data)[0])) by {
        transport(at(function.entry, separate(memory(at(call(1).exit, call(1).result)[0]), memory(old(this->data)[0]))), separate(memory(at(call(1).exit, call(1).result)[0]), memory(old(this->data)[0]))) using {
        };
    }
    have separate(region(11).footprint, memory(old(this->data)[0])) by {
        normalize() using {
            separate(memory(at(call(1).exit, call(1).result)[0]), memory(old(this->data)[0]));
        };
    }
    have at(region(11).exit, load_uint8((old(this->data) + 0))) == at(region(11).entry, load_uint8((old(this->data) + 0))) by {
        preserve(memory(old(this->data)[0]), region(11));
    }
    have load_uint8((old(this->data) + 0)) == old(this->data[0]) by {
        known();
    }
    have separate(memory(at(call(1).exit, call(1).result)[0]), memory(old(this->data)[1])) by {
        transport(at(function.entry, separate(memory(at(call(1).exit, call(1).result)[0]), memory(old(this->data)[1]))), separate(memory(at(call(1).exit, call(1).result)[0]), memory(old(this->data)[1]))) using {
        };
    }
    have separate(region(11).footprint, memory(old(this->data)[1])) by {
        normalize() using {
            separate(memory(at(call(1).exit, call(1).result)[0]), memory(old(this->data)[1]));
        };
    }
    have at(region(11).exit, load_uint8((old(this->data) + 1))) == at(region(11).entry, load_uint8((old(this->data) + 1))) by {
        preserve(memory(old(this->data)[1]), region(11));
    }
    have load_uint8((old(this->data) + 1)) == old(this->data[1]) by {
        known();
    }
    have separate(memory(old(dst->_M_ptr)[1]), memory(old(dst->_M_ptr)[0])) by {
        apply(click::separation::separate_elements(old(dst->_M_ptr), 1, 0)) using {
            1 != 0;
        };
    }
    have separate(memory(at(call(1).exit, call(1).result)[0]), memory(old(dst->_M_ptr)[0])) by {
        known();
    }
    have separate(region(11).footprint, memory(old(dst->_M_ptr)[0])) by {
        normalize() using {
            separate(memory(at(call(1).exit, call(1).result)[0]), memory(old(dst->_M_ptr)[0]));
        };
    }
    have at(region(11).exit, load_uint8((old(dst->_M_ptr) + 0))) == at(region(11).entry, load_uint8((old(dst->_M_ptr) + 0))) by {
        preserve(memory(old(dst->_M_ptr)[0]), region(11));
    }
    have load_uint8((old(dst->_M_ptr) + 0)) == old(this->data[0]) by {
        known();
    }
    have load_uint8((old(dst->_M_ptr) + 1)) == old(this->data[1]) by {
        known();
    }
    have separate(memory(at(call(1).exit, call(1).result)[0]), memory(old(this->data)[2])) by {
        transport(at(function.entry, separate(memory(at(call(1).exit, call(1).result)[0]), memory(old(this->data)[2]))), separate(memory(at(call(1).exit, call(1).result)[0]), memory(old(this->data)[2]))) using {
        };
    }
    have separate(region(11).footprint, memory(old(this->data)[2])) by {
        normalize() using {
            separate(memory(at(call(1).exit, call(1).result)[0]), memory(old(this->data)[2]));
        };
    }
    have at(region(11).exit, load_uint8((old(this->data) + 2))) == at(region(11).entry, load_uint8((old(this->data) + 2))) by {
        preserve(memory(old(this->data)[2]), region(11));
    }
    have load_uint8((old(this->data) + 2)) == old(this->data[2]) by {
        known();
    }
    have separate(memory(at(call(1).exit, call(1).result)[0]), memory(old(this->data)[3])) by {
        transport(at(function.entry, separate(memory(at(call(1).exit, call(1).result)[0]), memory(old(this->data)[3]))), separate(memory(at(call(1).exit, call(1).result)[0]), memory(old(this->data)[3]))) using {
        };
    }
    have separate(region(11).footprint, memory(old(this->data)[3])) by {
        normalize() using {
            separate(memory(at(call(1).exit, call(1).result)[0]), memory(old(this->data)[3]));
        };
    }
    have at(region(11).exit, load_uint8((old(this->data) + 3))) == at(region(11).entry, load_uint8((old(this->data) + 3))) by {
        preserve(memory(old(this->data)[3]), region(11));
    }
    have load_uint8((old(this->data) + 3)) == old(this->data[3]) by {
        known();
    }
    step();
    step();
    step();
    step() by {
        have at(function.entry, 2u64) < at(function.entry, load_uint64(byte_offset(dst, 8))) by {
            rewrite(at(region(15).entry, at(region(13).exit, dst->_M_extent._M_extent_value)), at(region(15).entry, 4u64));
            known();
        }
        known();
    }
    have call(2).result == (old(dst->_M_ptr) + 2) by {
        known();
    }
    step();
    step() by {
        known();
    }
    have separate(memory(at(call(2).exit, call(2).result)[0]), memory(this->data)) by {
        known();
    }
    have separate(region(17).footprint, memory(this->data)) by {
        normalize() using {
            separate(memory(at(call(2).exit, call(2).result)[0]), memory(this->data));
        };
    }
    have at(region(17).exit, this->data) == at(region(17).entry, this->data) by {
        preserve(memory(this->data), region(17));
    }
    have this->data == old(this->data) by {
        known();
    }
    have separate(memory(at(call(2).exit, call(2).result)[0]), memory(this->remaining)) by {
        known();
    }
    have separate(region(17).footprint, memory(this->remaining)) by {
        normalize() using {
            separate(memory(at(call(2).exit, call(2).result)[0]), memory(this->remaining));
        };
    }
    have at(region(17).exit, this->remaining) == at(region(17).entry, this->remaining) by {
        preserve(memory(this->remaining), region(17));
    }
    have this->remaining == old(this->remaining) by {
        known();
    }
    have separate(memory(at(call(2).exit, call(2).result)[0]), memory(old(this->data)[0])) by {
        transport(at(function.entry, separate(memory(at(call(2).exit, call(2).result)[0]), memory(old(this->data)[0]))), separate(memory(at(call(2).exit, call(2).result)[0]), memory(old(this->data)[0]))) using {
        };
    }
    have separate(region(17).footprint, memory(old(this->data)[0])) by {
        normalize() using {
            separate(memory(at(call(2).exit, call(2).result)[0]), memory(old(this->data)[0]));
        };
    }
    have at(region(17).exit, load_uint8((old(this->data) + 0))) == at(region(17).entry, load_uint8((old(this->data) + 0))) by {
        preserve(memory(old(this->data)[0]), region(17));
    }
    have load_uint8((old(this->data) + 0)) == old(this->data[0]) by {
        known();
    }
    have separate(memory(at(call(2).exit, call(2).result)[0]), memory(old(this->data)[1])) by {
        transport(at(function.entry, separate(memory(at(call(2).exit, call(2).result)[0]), memory(old(this->data)[1]))), separate(memory(at(call(2).exit, call(2).result)[0]), memory(old(this->data)[1]))) using {
        };
    }
    have separate(region(17).footprint, memory(old(this->data)[1])) by {
        normalize() using {
            separate(memory(at(call(2).exit, call(2).result)[0]), memory(old(this->data)[1]));
        };
    }
    have at(region(17).exit, load_uint8((old(this->data) + 1))) == at(region(17).entry, load_uint8((old(this->data) + 1))) by {
        preserve(memory(old(this->data)[1]), region(17));
    }
    have load_uint8((old(this->data) + 1)) == old(this->data[1]) by {
        known();
    }
    have separate(memory(at(call(2).exit, call(2).result)[0]), memory(old(this->data)[2])) by {
        transport(at(function.entry, separate(memory(at(call(2).exit, call(2).result)[0]), memory(old(this->data)[2]))), separate(memory(at(call(2).exit, call(2).result)[0]), memory(old(this->data)[2]))) using {
        };
    }
    have separate(region(17).footprint, memory(old(this->data)[2])) by {
        normalize() using {
            separate(memory(at(call(2).exit, call(2).result)[0]), memory(old(this->data)[2]));
        };
    }
    have at(region(17).exit, load_uint8((old(this->data) + 2))) == at(region(17).entry, load_uint8((old(this->data) + 2))) by {
        preserve(memory(old(this->data)[2]), region(17));
    }
    have load_uint8((old(this->data) + 2)) == old(this->data[2]) by {
        known();
    }
    have separate(memory(old(dst->_M_ptr)[2]), memory(old(dst->_M_ptr)[0])) by {
        apply(click::separation::separate_elements(old(dst->_M_ptr), 2, 0)) using {
            2 != 0;
        };
    }
    have separate(memory(at(call(2).exit, call(2).result)[0]), memory(old(dst->_M_ptr)[0])) by {
        known();
    }
    have separate(region(17).footprint, memory(old(dst->_M_ptr)[0])) by {
        normalize() using {
            separate(memory(at(call(2).exit, call(2).result)[0]), memory(old(dst->_M_ptr)[0]));
        };
    }
    have at(region(17).exit, load_uint8((old(dst->_M_ptr) + 0))) == at(region(17).entry, load_uint8((old(dst->_M_ptr) + 0))) by {
        preserve(memory(old(dst->_M_ptr)[0]), region(17));
    }
    have load_uint8((old(dst->_M_ptr) + 0)) == old(this->data[0]) by {
        known();
    }
    have separate(memory(old(dst->_M_ptr)[2]), memory(old(dst->_M_ptr)[1])) by {
        apply(click::separation::separate_elements(old(dst->_M_ptr), 2, 1)) using {
            2 != 1;
        };
    }
    have separate(memory(at(call(2).exit, call(2).result)[0]), memory(old(dst->_M_ptr)[1])) by {
        known();
    }
    have separate(region(17).footprint, memory(old(dst->_M_ptr)[1])) by {
        normalize() using {
            separate(memory(at(call(2).exit, call(2).result)[0]), memory(old(dst->_M_ptr)[1]));
        };
    }
    have at(region(17).exit, load_uint8((old(dst->_M_ptr) + 1))) == at(region(17).entry, load_uint8((old(dst->_M_ptr) + 1))) by {
        preserve(memory(old(dst->_M_ptr)[1]), region(17));
    }
    have load_uint8((old(dst->_M_ptr) + 1)) == old(this->data[1]) by {
        known();
    }
    have load_uint8((old(dst->_M_ptr) + 2)) == old(this->data[2]) by {
        known();
    }
    have separate(memory(at(call(2).exit, call(2).result)[0]), memory(old(this->data)[3])) by {
        transport(at(function.entry, separate(memory(at(call(2).exit, call(2).result)[0]), memory(old(this->data)[3]))), separate(memory(at(call(2).exit, call(2).result)[0]), memory(old(this->data)[3]))) using {
        };
    }
    have separate(region(17).footprint, memory(old(this->data)[3])) by {
        normalize() using {
            separate(memory(at(call(2).exit, call(2).result)[0]), memory(old(this->data)[3]));
        };
    }
    have at(region(17).exit, load_uint8((old(this->data) + 3))) == at(region(17).entry, load_uint8((old(this->data) + 3))) by {
        preserve(memory(old(this->data)[3]), region(17));
    }
    have load_uint8((old(this->data) + 3)) == old(this->data[3]) by {
        known();
    }
    step();
    step();
    step();
    step() by {
        have at(function.entry, 3u64) < at(function.entry, load_uint64(byte_offset(dst, 8))) by {
            rewrite(at(region(21).entry, at(region(19).exit, dst->_M_extent._M_extent_value)), at(region(21).entry, 4u64));
            known();
        }
        known();
    }
    have call(3).result == (old(dst->_M_ptr) + 3) by {
        known();
    }
    step();
    step() by {
        known();
    }
    have separate(memory(at(call(3).exit, call(3).result)[0]), memory(this->data)) by {
        known();
    }
    have separate(region(23).footprint, memory(this->data)) by {
        normalize() using {
            separate(memory(at(call(3).exit, call(3).result)[0]), memory(this->data));
        };
    }
    have at(region(23).exit, this->data) == at(region(23).entry, this->data) by {
        preserve(memory(this->data), region(23));
    }
    have this->data == old(this->data) by {
        known();
    }
    have separate(memory(at(call(3).exit, call(3).result)[0]), memory(this->remaining)) by {
        known();
    }
    have separate(region(23).footprint, memory(this->remaining)) by {
        normalize() using {
            separate(memory(at(call(3).exit, call(3).result)[0]), memory(this->remaining));
        };
    }
    have at(region(23).exit, this->remaining) == at(region(23).entry, this->remaining) by {
        preserve(memory(this->remaining), region(23));
    }
    have this->remaining == old(this->remaining) by {
        known();
    }
    have separate(memory(at(call(3).exit, call(3).result)[0]), memory(old(this->data)[0])) by {
        transport(at(function.entry, separate(memory(at(call(3).exit, call(3).result)[0]), memory(old(this->data)[0]))), separate(memory(at(call(3).exit, call(3).result)[0]), memory(old(this->data)[0]))) using {
        };
    }
    have separate(region(23).footprint, memory(old(this->data)[0])) by {
        normalize() using {
            separate(memory(at(call(3).exit, call(3).result)[0]), memory(old(this->data)[0]));
        };
    }
    have at(region(23).exit, load_uint8((old(this->data) + 0))) == at(region(23).entry, load_uint8((old(this->data) + 0))) by {
        preserve(memory(old(this->data)[0]), region(23));
    }
    have load_uint8((old(this->data) + 0)) == old(this->data[0]) by {
        known();
    }
    have separate(memory(at(call(3).exit, call(3).result)[0]), memory(old(this->data)[1])) by {
        transport(at(function.entry, separate(memory(at(call(3).exit, call(3).result)[0]), memory(old(this->data)[1]))), separate(memory(at(call(3).exit, call(3).result)[0]), memory(old(this->data)[1]))) using {
        };
    }
    have separate(region(23).footprint, memory(old(this->data)[1])) by {
        normalize() using {
            separate(memory(at(call(3).exit, call(3).result)[0]), memory(old(this->data)[1]));
        };
    }
    have at(region(23).exit, load_uint8((old(this->data) + 1))) == at(region(23).entry, load_uint8((old(this->data) + 1))) by {
        preserve(memory(old(this->data)[1]), region(23));
    }
    have load_uint8((old(this->data) + 1)) == old(this->data[1]) by {
        known();
    }
    have separate(memory(at(call(3).exit, call(3).result)[0]), memory(old(this->data)[2])) by {
        transport(at(function.entry, separate(memory(at(call(3).exit, call(3).result)[0]), memory(old(this->data)[2]))), separate(memory(at(call(3).exit, call(3).result)[0]), memory(old(this->data)[2]))) using {
        };
    }
    have separate(region(23).footprint, memory(old(this->data)[2])) by {
        normalize() using {
            separate(memory(at(call(3).exit, call(3).result)[0]), memory(old(this->data)[2]));
        };
    }
    have at(region(23).exit, load_uint8((old(this->data) + 2))) == at(region(23).entry, load_uint8((old(this->data) + 2))) by {
        preserve(memory(old(this->data)[2]), region(23));
    }
    have load_uint8((old(this->data) + 2)) == old(this->data[2]) by {
        known();
    }
    have separate(memory(at(call(3).exit, call(3).result)[0]), memory(old(this->data)[3])) by {
        transport(at(function.entry, separate(memory(at(call(3).exit, call(3).result)[0]), memory(old(this->data)[3]))), separate(memory(at(call(3).exit, call(3).result)[0]), memory(old(this->data)[3]))) using {
        };
    }
    have separate(region(23).footprint, memory(old(this->data)[3])) by {
        normalize() using {
            separate(memory(at(call(3).exit, call(3).result)[0]), memory(old(this->data)[3]));
        };
    }
    have at(region(23).exit, load_uint8((old(this->data) + 3))) == at(region(23).entry, load_uint8((old(this->data) + 3))) by {
        preserve(memory(old(this->data)[3]), region(23));
    }
    have load_uint8((old(this->data) + 3)) == old(this->data[3]) by {
        known();
    }
    have separate(memory(old(dst->_M_ptr)[3]), memory(old(dst->_M_ptr)[0])) by {
        apply(click::separation::separate_elements(old(dst->_M_ptr), 3, 0)) using {
            3 != 0;
        };
    }
    have separate(memory(at(call(3).exit, call(3).result)[0]), memory(old(dst->_M_ptr)[0])) by {
        known();
    }
    have separate(region(23).footprint, memory(old(dst->_M_ptr)[0])) by {
        normalize() using {
            separate(memory(at(call(3).exit, call(3).result)[0]), memory(old(dst->_M_ptr)[0]));
        };
    }
    have at(region(23).exit, load_uint8((old(dst->_M_ptr) + 0))) == at(region(23).entry, load_uint8((old(dst->_M_ptr) + 0))) by {
        preserve(memory(old(dst->_M_ptr)[0]), region(23));
    }
    have load_uint8((old(dst->_M_ptr) + 0)) == old(this->data[0]) by {
        known();
    }
    have separate(memory(old(dst->_M_ptr)[3]), memory(old(dst->_M_ptr)[1])) by {
        apply(click::separation::separate_elements(old(dst->_M_ptr), 3, 1)) using {
            3 != 1;
        };
    }
    have separate(memory(at(call(3).exit, call(3).result)[0]), memory(old(dst->_M_ptr)[1])) by {
        known();
    }
    have separate(region(23).footprint, memory(old(dst->_M_ptr)[1])) by {
        normalize() using {
            separate(memory(at(call(3).exit, call(3).result)[0]), memory(old(dst->_M_ptr)[1]));
        };
    }
    have at(region(23).exit, load_uint8((old(dst->_M_ptr) + 1))) == at(region(23).entry, load_uint8((old(dst->_M_ptr) + 1))) by {
        preserve(memory(old(dst->_M_ptr)[1]), region(23));
    }
    have load_uint8((old(dst->_M_ptr) + 1)) == old(this->data[1]) by {
        known();
    }
    have separate(memory(old(dst->_M_ptr)[3]), memory(old(dst->_M_ptr)[2])) by {
        apply(click::separation::separate_elements(old(dst->_M_ptr), 3, 2)) using {
            3 != 2;
        };
    }
    have separate(memory(at(call(3).exit, call(3).result)[0]), memory(old(dst->_M_ptr)[2])) by {
        known();
    }
    have separate(region(23).footprint, memory(old(dst->_M_ptr)[2])) by {
        normalize() using {
            separate(memory(at(call(3).exit, call(3).result)[0]), memory(old(dst->_M_ptr)[2]));
        };
    }
    have at(region(23).exit, load_uint8((old(dst->_M_ptr) + 2))) == at(region(23).entry, load_uint8((old(dst->_M_ptr) + 2))) by {
        preserve(memory(old(dst->_M_ptr)[2]), region(23));
    }
    have load_uint8((old(dst->_M_ptr) + 2)) == old(this->data[2]) by {
        known();
    }
    have load_uint8((old(dst->_M_ptr) + 3)) == old(this->data[3]) by {
        known();
    }
    step() by {
        known();
    }
    step() by {
        known();
    }
    step();
    have separate(memory(this->data), memory(old(dst->_M_ptr)[0])) by {
        known();
    }
    have separate(region(24).footprint, memory(old(dst->_M_ptr)[0])) by {
        normalize() using {
            separate(memory(this->data), memory(old(dst->_M_ptr)[0]));
        };
    }
    have at(region(24).exit, load_uint8((old(dst->_M_ptr) + 0))) == at(region(24).entry, load_uint8((old(dst->_M_ptr) + 0))) by {
        preserve(memory(old(dst->_M_ptr)[0]), region(24));
    }
    have at(region(24).exit, load_uint8((old(dst->_M_ptr) + 0))) == old(this->data[0]) by {
        known();
    }
    have separate(memory(this->data), memory(old(dst->_M_ptr)[1])) by {
        known();
    }
    have separate(region(24).footprint, memory(old(dst->_M_ptr)[1])) by {
        normalize() using {
            separate(memory(this->data), memory(old(dst->_M_ptr)[1]));
        };
    }
    have at(region(24).exit, load_uint8((old(dst->_M_ptr) + 1))) == at(region(24).entry, load_uint8((old(dst->_M_ptr) + 1))) by {
        preserve(memory(old(dst->_M_ptr)[1]), region(24));
    }
    have at(region(24).exit, load_uint8((old(dst->_M_ptr) + 1))) == old(this->data[1]) by {
        known();
    }
    have separate(memory(this->data), memory(old(dst->_M_ptr)[2])) by {
        known();
    }
    have separate(region(24).footprint, memory(old(dst->_M_ptr)[2])) by {
        normalize() using {
            separate(memory(this->data), memory(old(dst->_M_ptr)[2]));
        };
    }
    have at(region(24).exit, load_uint8((old(dst->_M_ptr) + 2))) == at(region(24).entry, load_uint8((old(dst->_M_ptr) + 2))) by {
        preserve(memory(old(dst->_M_ptr)[2]), region(24));
    }
    have at(region(24).exit, load_uint8((old(dst->_M_ptr) + 2))) == old(this->data[2]) by {
        known();
    }
    have separate(memory(this->data), memory(old(dst->_M_ptr)[3])) by {
        known();
    }
    have separate(region(24).footprint, memory(old(dst->_M_ptr)[3])) by {
        normalize() using {
            separate(memory(this->data), memory(old(dst->_M_ptr)[3]));
        };
    }
    have at(region(24).exit, load_uint8((old(dst->_M_ptr) + 3))) == at(region(24).entry, load_uint8((old(dst->_M_ptr) + 3))) by {
        preserve(memory(old(dst->_M_ptr)[3]), region(24));
    }
    have at(region(24).exit, load_uint8((old(dst->_M_ptr) + 3))) == old(this->data[3]) by {
        known();
    }
    have separate(memory(this->remaining), memory(old(dst->_M_ptr)[0])) by {
        known();
    }
    have separate(region(25).footprint, memory(old(dst->_M_ptr)[0])) by {
        normalize() using {
            separate(memory(this->remaining), memory(old(dst->_M_ptr)[0]));
        };
    }
    have at(region(25).exit, load_uint8((old(dst->_M_ptr) + 0))) == at(region(25).entry, load_uint8((old(dst->_M_ptr) + 0))) by {
        preserve(memory(old(dst->_M_ptr)[0]), region(25));
    }
    have at(region(25).exit, load_uint8((old(dst->_M_ptr) + 0))) == old(this->data[0]) by {
        known();
    }
    have separate(memory(this->remaining), memory(old(dst->_M_ptr)[1])) by {
        known();
    }
    have separate(region(25).footprint, memory(old(dst->_M_ptr)[1])) by {
        normalize() using {
            separate(memory(this->remaining), memory(old(dst->_M_ptr)[1]));
        };
    }
    have at(region(25).exit, load_uint8((old(dst->_M_ptr) + 1))) == at(region(25).entry, load_uint8((old(dst->_M_ptr) + 1))) by {
        preserve(memory(old(dst->_M_ptr)[1]), region(25));
    }
    have at(region(25).exit, load_uint8((old(dst->_M_ptr) + 1))) == old(this->data[1]) by {
        known();
    }
    have separate(memory(this->remaining), memory(old(dst->_M_ptr)[2])) by {
        known();
    }
    have separate(region(25).footprint, memory(old(dst->_M_ptr)[2])) by {
        normalize() using {
            separate(memory(this->remaining), memory(old(dst->_M_ptr)[2]));
        };
    }
    have at(region(25).exit, load_uint8((old(dst->_M_ptr) + 2))) == at(region(25).entry, load_uint8((old(dst->_M_ptr) + 2))) by {
        preserve(memory(old(dst->_M_ptr)[2]), region(25));
    }
    have at(region(25).exit, load_uint8((old(dst->_M_ptr) + 2))) == old(this->data[2]) by {
        known();
    }
    have separate(memory(this->remaining), memory(old(dst->_M_ptr)[3])) by {
        known();
    }
    have separate(region(25).footprint, memory(old(dst->_M_ptr)[3])) by {
        normalize() using {
            separate(memory(this->remaining), memory(old(dst->_M_ptr)[3]));
        };
    }
    have at(region(25).exit, load_uint8((old(dst->_M_ptr) + 3))) == at(region(25).entry, load_uint8((old(dst->_M_ptr) + 3))) by {
        preserve(memory(old(dst->_M_ptr)[3]), region(25));
    }
    have at(region(25).exit, load_uint8((old(dst->_M_ptr) + 3))) == old(this->data[3]) by {
        known();
    }
    have separate(memory(this->data), memory(old(this->data)[0])) by {
        known();
    }
    have separate(region(24).footprint, memory(old(this->data)[0])) by {
        normalize() using {
            separate(memory(this->data), memory(old(this->data)[0]));
        };
    }
    have at(region(24).exit, load_uint8((old(this->data) + 0))) == at(region(24).entry, load_uint8((old(this->data) + 0))) by {
        preserve(memory(old(this->data)[0]), region(24));
    }
    have at(region(24).exit, load_uint8((old(this->data) + 0))) == old(this->data[0]) by {
        known();
    }
    have separate(memory(this->data), memory(old(this->data)[1])) by {
        known();
    }
    have separate(region(24).footprint, memory(old(this->data)[1])) by {
        normalize() using {
            separate(memory(this->data), memory(old(this->data)[1]));
        };
    }
    have at(region(24).exit, load_uint8((old(this->data) + 1))) == at(region(24).entry, load_uint8((old(this->data) + 1))) by {
        preserve(memory(old(this->data)[1]), region(24));
    }
    have at(region(24).exit, load_uint8((old(this->data) + 1))) == old(this->data[1]) by {
        known();
    }
    have separate(memory(this->data), memory(old(this->data)[2])) by {
        known();
    }
    have separate(region(24).footprint, memory(old(this->data)[2])) by {
        normalize() using {
            separate(memory(this->data), memory(old(this->data)[2]));
        };
    }
    have at(region(24).exit, load_uint8((old(this->data) + 2))) == at(region(24).entry, load_uint8((old(this->data) + 2))) by {
        preserve(memory(old(this->data)[2]), region(24));
    }
    have at(region(24).exit, load_uint8((old(this->data) + 2))) == old(this->data[2]) by {
        known();
    }
    have separate(memory(this->data), memory(old(this->data)[3])) by {
        known();
    }
    have separate(region(24).footprint, memory(old(this->data)[3])) by {
        normalize() using {
            separate(memory(this->data), memory(old(this->data)[3]));
        };
    }
    have at(region(24).exit, load_uint8((old(this->data) + 3))) == at(region(24).entry, load_uint8((old(this->data) + 3))) by {
        preserve(memory(old(this->data)[3]), region(24));
    }
    have at(region(24).exit, load_uint8((old(this->data) + 3))) == old(this->data[3]) by {
        known();
    }
    have separate(memory(this->remaining), memory(old(this->data)[0])) by {
        known();
    }
    have separate(region(25).footprint, memory(old(this->data)[0])) by {
        normalize() using {
            separate(memory(this->remaining), memory(old(this->data)[0]));
        };
    }
    have at(region(25).exit, load_uint8((old(this->data) + 0))) == at(region(25).entry, load_uint8((old(this->data) + 0))) by {
        preserve(memory(old(this->data)[0]), region(25));
    }
    have at(region(25).exit, load_uint8((old(this->data) + 0))) == old(this->data[0]) by {
        known();
    }
    have separate(memory(this->remaining), memory(old(this->data)[1])) by {
        known();
    }
    have separate(region(25).footprint, memory(old(this->data)[1])) by {
        normalize() using {
            separate(memory(this->remaining), memory(old(this->data)[1]));
        };
    }
    have at(region(25).exit, load_uint8((old(this->data) + 1))) == at(region(25).entry, load_uint8((old(this->data) + 1))) by {
        preserve(memory(old(this->data)[1]), region(25));
    }
    have at(region(25).exit, load_uint8((old(this->data) + 1))) == old(this->data[1]) by {
        known();
    }
    have separate(memory(this->remaining), memory(old(this->data)[2])) by {
        known();
    }
    have separate(region(25).footprint, memory(old(this->data)[2])) by {
        normalize() using {
            separate(memory(this->remaining), memory(old(this->data)[2]));
        };
    }
    have at(region(25).exit, load_uint8((old(this->data) + 2))) == at(region(25).entry, load_uint8((old(this->data) + 2))) by {
        preserve(memory(old(this->data)[2]), region(25));
    }
    have at(region(25).exit, load_uint8((old(this->data) + 2))) == old(this->data[2]) by {
        known();
    }
    have separate(memory(this->remaining), memory(old(this->data)[3])) by {
        known();
    }
    have separate(region(25).footprint, memory(old(this->data)[3])) by {
        normalize() using {
            separate(memory(this->remaining), memory(old(this->data)[3]));
        };
    }
    have at(region(25).exit, load_uint8((old(this->data) + 3))) == at(region(25).entry, load_uint8((old(this->data) + 3))) by {
        preserve(memory(old(this->data)[3]), region(25));
    }
    have at(region(25).exit, load_uint8((old(this->data) + 3))) == old(this->data[3]) by {
        known();
    }
    have separate(memory(this->data), memory(this->remaining)) by {
        known();
    }
    have separate(region(24).footprint, memory(this->remaining)) by {
        normalize() using {
            separate(memory(this->data), memory(this->remaining));
        };
    }
    have at(region(24).exit, this->remaining) == at(region(24).entry, this->remaining) by {
        preserve(memory(this->remaining), region(24));
    }
    have at(region(24).exit, this->remaining) == old(this->remaining) by {
        known();
    }
    have to_integer(this->remaining) == (to_integer(old(this->remaining)) - to_integer(4u64)) by {
        have (let integer_value: Integer = to_integer(((at(region(25).entry, load_uint64(byte_offset(this, 8))) - 4u64) as uint64)); integer_value) == (to_integer(old((load_uint64(byte_offset(this, 8)) as uint64))) - 4) by {
            have 0 <= (to_integer(at(region(25).entry, load_uint64(byte_offset(this, 8)))) - 4) by {
                have 0 <= (to_integer(at(region(25).entry, load_uint64(byte_offset(this, 8)))) - 4) by {
                    have ((-1 * old(to_integer(this->remaining))) + at(region(24).exit, to_integer(this->remaining))) == 0 by {
                        have at(region(24).exit, to_integer(this->remaining)) == old(to_integer(this->remaining)) by {
                            normalize() using {
                                at(region(24).exit, this->remaining) == old(this->remaining);
                            };
                        }
                        have (at(region(24).exit, to_integer(this->remaining)) - old(to_integer(this->remaining))) == 0 by {
                            apply(click::integer::equal_difference(at(region(24).exit, to_integer(this->remaining)), old(to_integer(this->remaining)))) using {
                                at(region(24).exit, to_integer(this->remaining)) ==
                                    old(to_integer(this->remaining));
                            };
                        }
                        have ((-1 * old(to_integer(this->remaining))) + at(region(24).exit, to_integer(this->remaining))) == (at(region(24).exit, to_integer(this->remaining)) - old(to_integer(this->remaining))) by {
                            normalize();
                        }
                        apply(click::integer::equal_substitute((at(region(24).exit, to_integer(this->remaining)) - old(to_integer(this->remaining))), 0, ((-1 * old(to_integer(this->remaining))) + at(region(24).exit, to_integer(this->remaining))), 0)) using {
                            (at(region(24).exit, to_integer(this->remaining)) -
                                old(to_integer(this->remaining))) == 0;
                            ((-1 * old(to_integer(this->remaining))) + at(region(24).exit,
                                to_integer(this->remaining))) == (at(region(24).exit,
                                to_integer(this->remaining)) - old(to_integer(this->remaining)));
                            (let integer_value: Integer = 0; integer_value) == 0;
                        };
                    }
                    have (old(to_integer(this->remaining)) + (-1 * at(region(24).exit, to_integer(this->remaining)))) <= 0 by {
                        have (((-1 * old(to_integer(this->remaining))) + at(region(24).exit, to_integer(this->remaining))) * -1) == (0 * -1) by {
                            apply(click::integer::equal_multiply(((-1 * old(to_integer(this->remaining))) + at(region(24).exit, to_integer(this->remaining))), 0, -1)) using {
                                ((-1 * old(to_integer(this->remaining))) + at(region(24).exit,
                                    to_integer(this->remaining))) == 0;
                            };
                        }
                        have (old(to_integer(this->remaining)) + (-1 * at(region(24).exit, to_integer(this->remaining)))) == 0 by {
                            have (old(to_integer(this->remaining)) + (-1 * at(region(24).exit, to_integer(this->remaining)))) == (((-1 * old(to_integer(this->remaining))) + at(region(24).exit, to_integer(this->remaining))) * -1) by {
                                normalize();
                            }
                            have (let integer_value: Integer = 0; integer_value) == (0 * -1) by {
                                normalize();
                            }
                            apply(click::integer::equal_substitute((((-1 * old(to_integer(this->remaining))) + at(region(24).exit, to_integer(this->remaining))) * -1), (0 * -1), (old(to_integer(this->remaining)) + (-1 * at(region(24).exit, to_integer(this->remaining)))), 0)) using {
                                (((-1 * old(to_integer(this->remaining))) + at(region(24).exit,
                                    to_integer(this->remaining))) * -1) == (0 * -1);
                                (old(to_integer(this->remaining)) + (-1 * at(region(24).exit,
                                    to_integer(this->remaining)))) == (((-1 *
                                    old(to_integer(this->remaining))) + at(region(24).exit,
                                    to_integer(this->remaining))) * -1);
                                (let integer_value: Integer = 0; integer_value) == (0 * -1);
                            };
                        }
                        apply(click::integer::equal_le((old(to_integer(this->remaining)) + (-1 * at(region(24).exit, to_integer(this->remaining)))), 0)) using {
                            (old(to_integer(this->remaining)) + (-1 * at(region(24).exit,
                                to_integer(this->remaining)))) == 0;
                        };
                    }
                    have ((-1 * old(to_integer(this->remaining))) + 4) <= 0 by {
                        have 4 <= at(function.entry, to_integer(this->remaining)) by {
                            normalize() using {
                                at(function.entry, 4u64 <= this->remaining);
                            };
                        }
                        have ((-1 * old(to_integer(this->remaining))) + 4) == (4 - at(function.entry, to_integer(this->remaining))) by {
                            normalize();
                        }
                        apply(click::integer::le_difference(4, at(function.entry, to_integer(this->remaining)), ((-1 * old(to_integer(this->remaining))) + 4))) using {
                            4 <= at(function.entry, to_integer(this->remaining));
                            ((-1 * old(to_integer(this->remaining))) + 4) == (4 - at(function.entry,
                                to_integer(this->remaining)));
                        };
                    }
                    have ((-1 * at(region(24).exit, to_integer(this->remaining))) + 4) <= 0 by {
                        have (old(to_integer(this->remaining)) + (-1 * at(region(24).exit, to_integer(this->remaining))) + ((-1 * old(to_integer(this->remaining))) + 4)) <= (0 + 0) by {
                            apply(click::integer::add_le((old(to_integer(this->remaining)) + (-1 * at(region(24).exit, to_integer(this->remaining)))), 0, ((-1 * old(to_integer(this->remaining))) + 4), 0)) using {
                                (old(to_integer(this->remaining)) + (-1 * at(region(24).exit,
                                    to_integer(this->remaining)))) <= 0;
                                ((-1 * old(to_integer(this->remaining))) + 4) <= 0;
                            };
                        }
                        have ((-1 * at(region(24).exit, to_integer(this->remaining))) + 4) == (old(to_integer(this->remaining)) + (-1 * at(region(24).exit, to_integer(this->remaining))) + ((-1 * old(to_integer(this->remaining))) + 4)) by {
                            normalize();
                        }
                        have (let integer_value: Integer = 0; integer_value) == (0 + 0) by {
                            normalize();
                        }
                        apply(click::integer::le_substitute((old(to_integer(this->remaining)) + (-1 * at(region(24).exit, to_integer(this->remaining))) + ((-1 * old(to_integer(this->remaining))) + 4)), (0 + 0), ((-1 * at(region(24).exit, to_integer(this->remaining))) + 4), 0)) using {
                            (old(to_integer(this->remaining)) + (-1 * at(region(24).exit,
                                to_integer(this->remaining))) + ((-1 *
                                old(to_integer(this->remaining))) + 4)) <= (0 + 0);
                            ((-1 * at(region(24).exit, to_integer(this->remaining))) + 4) ==
                                (old(to_integer(this->remaining)) + (-1 * at(region(24).exit,
                                to_integer(this->remaining))) + ((-1 *
                                old(to_integer(this->remaining))) + 4));
                            (let integer_value: Integer = 0; integer_value) == (0 + 0);
                        };
                    }
                    have ((-1 * at(region(24).exit, to_integer(this->remaining))) + 4) == (0 - (to_integer(at(region(25).entry, load_uint64(byte_offset(this, 8)))) - 4)) by {
                        normalize();
                    }
                    apply(click::integer::difference_le(0, (to_integer(at(region(25).entry, load_uint64(byte_offset(this, 8)))) - 4), ((-1 * at(region(24).exit, to_integer(this->remaining))) + 4))) using {
                        ((-1 * at(region(24).exit, to_integer(this->remaining))) + 4) <= 0;
                        ((-1 * at(region(24).exit, to_integer(this->remaining))) + 4) == (0 -
                            (to_integer(at(region(25).entry, load_uint64(byte_offset(this, 8)))) -
                            4));
                    };
                }
                normalize() using {
                    0 <= (to_integer(at(region(25).entry, load_uint64(byte_offset(this, 8)))) - 4);
                };
            }
            have (to_integer(at(region(25).entry, load_uint64(byte_offset(this, 8)))) - 4) <= 18446744073709551615 by {
                have (to_integer(at(region(25).entry, load_uint64(byte_offset(this, 8)))) - 4) <= 18446744073709551615 by {
                    have (to_integer(at(region(25).entry, load_uint64(byte_offset(this, 8)))) + -18446744073709551615) <= 0 by {
                        have to_integer(at(region(25).entry, load_uint64(byte_offset(this, 8)))) <= 18446744073709551615 by {
                            normalize();
                        }
                        have to_integer(at(region(25).entry, load_uint64(byte_offset(this, 8)))) <= to_integer(18446744073709551615u64) by {
                            normalize() using {
                                to_integer(at(region(25).entry, load_uint64(byte_offset(this, 8))))
                                    <= 18446744073709551615;
                            };
                        }
                        have (to_integer(at(region(25).entry, load_uint64(byte_offset(this, 8)))) + -18446744073709551615) == (to_integer(at(region(25).entry, load_uint64(byte_offset(this, 8)))) - to_integer(18446744073709551615u64)) by {
                            normalize();
                        }
                        apply(click::integer::le_difference(to_integer(at(region(25).entry, load_uint64(byte_offset(this, 8)))), to_integer(18446744073709551615u64), (to_integer(at(region(25).entry, load_uint64(byte_offset(this, 8)))) + -18446744073709551615))) using {
                            to_integer(at(region(25).entry, load_uint64(byte_offset(this, 8)))) <=
                                to_integer(18446744073709551615u64);
                            (to_integer(at(region(25).entry, load_uint64(byte_offset(this, 8)))) +
                                -18446744073709551615) == (to_integer(at(region(25).entry,
                                load_uint64(byte_offset(this, 8)))) -
                                to_integer(18446744073709551615u64));
                        };
                    }
                    have (let integer_value: Integer = -4; integer_value) <= 0 by {
                        normalize();
                    }
                    have (to_integer(at(region(25).entry, load_uint64(byte_offset(this, 8)))) + -18446744073709551619) <= 0 by {
                        have (to_integer(at(region(25).entry, load_uint64(byte_offset(this, 8)))) + -18446744073709551615 + -4) <= (0 + 0) by {
                            apply(click::integer::add_le((to_integer(at(region(25).entry, load_uint64(byte_offset(this, 8)))) + -18446744073709551615), 0, -4, 0)) using {
                                (to_integer(at(region(25).entry, load_uint64(byte_offset(this, 8))))
                                    + -18446744073709551615) <= 0;
                                (let integer_value: Integer = -4; integer_value) <= 0;
                            };
                        }
                        have (to_integer(at(region(25).entry, load_uint64(byte_offset(this, 8)))) + -18446744073709551619) == (to_integer(at(region(25).entry, load_uint64(byte_offset(this, 8)))) + -18446744073709551615 + -4) by {
                            normalize();
                        }
                        have (let integer_value: Integer = 0; integer_value) == (0 + 0) by {
                            normalize();
                        }
                        apply(click::integer::le_substitute((to_integer(at(region(25).entry, load_uint64(byte_offset(this, 8)))) + -18446744073709551615 + -4), (0 + 0), (to_integer(at(region(25).entry, load_uint64(byte_offset(this, 8)))) + -18446744073709551619), 0)) using {
                            (to_integer(at(region(25).entry, load_uint64(byte_offset(this, 8)))) +
                                -18446744073709551615 + -4) <= (0 + 0);
                            (to_integer(at(region(25).entry, load_uint64(byte_offset(this, 8)))) +
                                -18446744073709551619) == (to_integer(at(region(25).entry,
                                load_uint64(byte_offset(this, 8)))) + -18446744073709551615 + -4);
                            (let integer_value: Integer = 0; integer_value) == (0 + 0);
                        };
                    }
                    have (to_integer(at(region(25).entry, load_uint64(byte_offset(this, 8)))) + -18446744073709551619) == ((to_integer(at(region(25).entry, load_uint64(byte_offset(this, 8)))) - 4) - 18446744073709551615) by {
                        normalize();
                    }
                    apply(click::integer::difference_le((to_integer(at(region(25).entry, load_uint64(byte_offset(this, 8)))) - 4), 18446744073709551615, (to_integer(at(region(25).entry, load_uint64(byte_offset(this, 8)))) + -18446744073709551619))) using {
                        (to_integer(at(region(25).entry, load_uint64(byte_offset(this, 8)))) +
                            -18446744073709551619) <= 0;
                        (to_integer(at(region(25).entry, load_uint64(byte_offset(this, 8)))) +
                            -18446744073709551619) == ((to_integer(at(region(25).entry,
                            load_uint64(byte_offset(this, 8)))) - 4) - 18446744073709551615);
                    };
                }
                normalize() using {
                    (to_integer(at(region(25).entry, load_uint64(byte_offset(this, 8)))) - 4) <=
                        18446744073709551615;
                };
            }
            have (let integer_value: Integer = to_integer(((at(region(25).entry, load_uint64(byte_offset(this, 8))) - 4u64) as uint64)); integer_value) == (to_integer(at(region(25).entry, load_uint64(byte_offset(this, 8)))) - 4) by {
                normalize() using {
                    0 <= (to_integer(at(region(25).entry, load_uint64(byte_offset(this, 8)))) - 4);
                    (to_integer(at(region(25).entry, load_uint64(byte_offset(this, 8)))) - 4) <=
                        18446744073709551615;
                };
            }
            known();
        }
        known();
    }
    known();
    have dst->_M_ptr[0] == old(this->data[0]) by {
        known();
    }
    have dst->_M_ptr[1] == old(this->data[1]) by {
        known();
    }
    have dst->_M_ptr[2] == old(this->data[2]) by {
        known();
    }
    have dst->_M_ptr[3] == old(this->data[3]) by {
        known();
    }
    have this->data == (old(this->data) + 4) by {
        known();
    }
    have to_integer(this->remaining) == (to_integer(old(this->remaining)) - to_integer(4u64)) by {
        known();
    }
    known();
    known();
    known();
    known();
    known();
    known();
    known();
    known();
    known();
    known();
    known();
}

uint32 le32toh_internal(uint32 little_endian_32bits) {
    ensures result == little_endian_32bits by {
        step();
        step();
        have result == little_endian_32bits by {
            known();
        }
        known();
        known();
        known();
        known();
    }
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
} by {
    step();
    step();
    step();
    step();
    step();
    have call(1).parameter(__sp)._M_extent._M_extent_value == 1u64 by {
        known();
    }
    have call(1).parameter(__sp)._M_ptr == &obj by {
        known();
    }
    have to_integer(call(1).result._M_extent._M_extent_value) == (to_integer(call(1).parameter(__sp)._M_extent._M_extent_value) * to_integer(4u64)) by {
        known();
    }
    have call(1).result._M_extent._M_extent_value == 4u64 by {
        rewrite(to_integer(call(1).result._M_extent._M_extent_value), (to_integer(call(1).parameter(__sp)._M_extent._M_extent_value) * to_integer(4u64)));
        rewrite(call(1).parameter(__sp)._M_extent._M_extent_value, 1u64);
        known();
    }
    have call(1).result._M_ptr == (&obj as (uint8 *)) by {
        known();
    }
    step() {
        requires call(2).parameter(dst)._M_extent._M_extent_value == 4u64 by {
            known();
        }
        requires 4u64 <= s.remaining by {
            known();
        }
        requires separate(memory(at(call(2).entry, call(2).parameter(dst)._M_ptr)[0..4]), memory(s.data[0..4])) by {
            transport(at(function.entry, separate(memory(at(call(2).entry, call(2).parameter(dst)._M_ptr)[0..4]), memory(s.data[0..4]))), separate(memory(at(call(2).entry, call(2).parameter(dst)._M_ptr)[0..4]), memory(s.data[0..4]))) using {
                at(function.entry, separate(memory(at(call(2).entry,
                    call(2).parameter(dst)._M_ptr)[0..4]), memory(s.data[0..4])));
            };
        }
    }
    have call(2).parameter(dst)._M_ptr == (&obj as (uint8 *)) by {
        known();
    }
    have (&obj as (uint8 *))[0] == 120u8 by {
        known();
    }
    have (&obj as (uint8 *))[1] == 86u8 by {
        known();
    }
    have (&obj as (uint8 *))[2] == 52u8 by {
        known();
    }
    have (&obj as (uint8 *))[3] == 18u8 by {
        known();
    }
    have obj == 305419896u32 by {
        known();
    }
    step();
    step();
    step();
    step();
    step();
    known();
    have result == 305419896u32 by {
        known();
    }
    have s.data == (old(s.data) + 4) by {
        known();
    }
    have to_integer(s.remaining) == (to_integer(old(s.remaining)) - to_integer(4u64)) by {
        known();
    }
    known();
    known();
    known();
    known();
    known();
    known();
    known();
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
} by {
    step();
    step() {
        requires 4u64 <= stream.remaining by {
            known();
        }
        requires stream.data[0] == 120u8 by {
            known();
        }
        requires stream.data[1] == 86u8 by {
            known();
        }
        requires stream.data[2] == 52u8 by {
            known();
        }
        requires stream.data[3] == 18u8 by {
            known();
        }
    }
    step();
    step();
    have result == 305419896u32 by {
        known();
    }
    have stream.data == (old(stream.data) + 4) by {
        known();
    }
    have to_integer(stream.remaining) == (to_integer(old(stream.remaining)) - to_integer(4u64)) by {
        known();
    }
    known();
    known();
    known();
    known();
    known();
    known();
    known();
    known();
}
