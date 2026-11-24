verifying "cJSON.c";
import click::integer;
import click::separation;

resource maybe_bytes(p: void*, n: uint64) {
    if p != 0 { owns (p as (uint8*))[0..n]; }
}

contract void* Allocate(uint64 size) {
    produces maybe_bytes(result, size);
}

cJSON_bool parse_string(cJSON * const item, parse_buffer * const input_buffer) {
    owns item->type;
    owns item->valuestring;
    owns input_buffer->offset;
    views input_buffer->content;
    views input_buffer->length;
    views input_buffer->hooks.allocate;
    requires Allocate(input_buffer->hooks.allocate);
    let content = input_buffer->content;
    let length = input_buffer->length;
    let offset = input_buffer->offset;
    requires offset + 1 < length;
    views content[0..length];
    requires content[offset] == 34;
    requires content[offset + 1] == 34;
    ensures result == 1 implies input_buffer->offset == old(input_buffer->offset) + 2;
} by {
    have input_buffer->offset < input_buffer->length by { solve(); }
    have to_integer(input_buffer->offset) + to_integer(1u64) <= 18446744073709551615 by { solve(); }
    apply(integer::uint64_add_to_integer(input_buffer->offset, 1u64));
    have to_integer(input_buffer->offset + 1u64) < to_integer(input_buffer->length) by { solve(); }
    have input_buffer->offset + 1u64 < input_buffer->length by { solve(); }
    apply(integer::uint8_pointer_add_associate_uint64(input_buffer->content, input_buffer->offset, 1u64));
    step_until(loop(0).entry);
    have program::input_end == input_buffer->content + (input_buffer->offset + 1u64) by { solve(); }
    apply(integer::uint8_pointer_add_address_uint64(input_buffer->content, input_buffer->offset + 1u64));
    have address(program::input_end) == ((address(input_buffer->content) + (input_buffer->offset + 1u64) * 1u64) as uint64) by { solve(); }
    have 0u64 < input_buffer->length by { solve(); }
    have 0u64 <= input_buffer->length by { solve(); }
    apply(separation::viewable_offset_nonnull(input_buffer->content, 0u64, input_buffer->length, 0u64));
    have input_buffer->content != 0 by { solve(); }
    have to_integer(input_buffer->offset) + 1 <= 9223372036854775807 by { solve(); }
    have to_integer(input_buffer->offset) <= 9223372036854775807 by { solve(); }
    have -9223372036854775808 <= to_integer(input_buffer->offset) by { solve(); }
    have to_integer(input_buffer->offset as int64) == to_integer(input_buffer->offset) by { known(); }
    have defined(input_buffer->offset as int64 + 1i64) by { solve(); }
    have to_integer(input_buffer->offset as int64 + 1i64) == to_integer(input_buffer->offset) + 1 by { solve(); }
    have to_integer(program::input_end - input_buffer->content) == to_integer(input_buffer->offset) + 1 by { solve(); }
    have (program::input_end - input_buffer->content) as uint64 < input_buffer->length by { solve(); }
    step();
    step();
    step();
    step();
    step();
    step();
    branch {
        true => {
            have input_buffer->offset + 1u64 <= input_buffer->length by { solve(); }
            apply(separation::viewable_offset_nonnull(input_buffer->content, 0u64, input_buffer->length, input_buffer->offset + 1u64));
            have program::input_pointer != 0 by { solve(); }
            step_until(function.exit);
        }
        false => {
            unfold(maybe_bytes(program::output, program::allocation_length + 1u64));
        }
    }
    step();
    step();
    step();
    have separate(memory(output[0..1]), memory(input_buffer->content)) by { solve(); }
    have separate(statement(8).footprint, memory(input_buffer->content)) by { solve(); }
    have input_buffer->content == at(statement(8).entry, input_buffer->content) by {
        preserve(memory(input_buffer->content), statement(8));
    }
    step();
    have separate(memory((item as (int32 *))[6..7]), memory(input_buffer->content)) by { solve(); }
    have separate(statement(9).footprint, memory(input_buffer->content)) by { known(); }
    have input_buffer->content == at(statement(9).entry, input_buffer->content) by {
        preserve(memory(input_buffer->content), statement(9));
    }
    step();
    have separate(memory((item as (uint8 *))[32..40]), memory(input_buffer->content)) by { solve(); }
    have separate(statement(10).footprint, memory(input_buffer->content)) by { known(); }
    have input_buffer->content == at(statement(10).entry, input_buffer->content) by {
        preserve(memory(input_buffer->content), statement(10));
    }
    have same_allocation(program::input_end, input_buffer->content) by { solve(); }
    have address(program::input_end) == ((address(old(input_buffer->content)) + (old(input_buffer->offset) + 1u64) * 1u64) as uint64) by { solve(); }
    have address(input_buffer->content) == address(old(input_buffer->content)) by { solve(); }
    have address(program::input_end) - address(input_buffer->content) == old(input_buffer->offset) + 1u64 by {
        rewrite(address(program::input_end), ((address(old(input_buffer->content)) + (old(input_buffer->offset) + 1u64) * 1u64) as uint64));
        rewrite(address(input_buffer->content), address(old(input_buffer->content)));
        apply(integer::uint64_add_subtract_cancel(address(old(input_buffer->content)), (old(input_buffer->offset) + 1u64) * 1u64));
        solve();
    }
    step();
    have input_buffer->offset == old(input_buffer->offset) + 1u64 by { solve(); }
    step();
    have to_integer(at(statement(11).exit, input_buffer->offset)) + to_integer(1u64) <= 18446744073709551615 by { solve(); }
    apply(integer::uint64_add_to_integer(at(statement(11).exit, input_buffer->offset), 1u64));
    have input_buffer->offset == at(statement(11).exit, input_buffer->offset) + 1u64 by { solve(); }
    have input_buffer->offset == old(input_buffer->offset) + 2u64 by { solve(); }
    have to_integer(input_buffer->offset) == to_integer(old(input_buffer->offset)) + 2 by { solve(); }
}
