verifying "fields.rs";
fn read(state: &Lanes, index: usize) -> u32 {
    requires index < 4u64;
    views state.values[0..4];
    ensures result == old(state.values[index]);
}
fn write(state: &mut Lanes, index: usize, value: u32) {
    requires index == 1u64;
    owns state.values[0..4];
    views state.marker;
    ensures state.values[index] == value;
    ensures state.values[0] == old(state.values[0]);
    ensures state.values[2] == old(state.values[2]);
    ensures state.values[3] == old(state.values[3]);
    ensures state.marker == old(state.marker);
} by {
    have (index as uint32 as int32) == 1 by { rewrite(index, 1u64); close(); }
    have separate(memory((((state as (void *)) as (uint32 *)) + index)[0..1]), memory(state.marker)) by {
        rewrite(index, 1u64);
        close();
    }
    have separate(memory((((state as (void *)) as (uint32 *)) + index)[0..1]), memory(*(((state as (void *)) as (uint32 *)) + 0u64))) by {
        rewrite(index, 1u64);
        close();
    }
    have separate(
        memory((((state as (void *)) as (uint32 *)) + index)[0..1]),
        memory(*(((state as (void *)) as (uint32 *)) + 2u64))
    ) by {
        rewrite(index, 1u64);
        close();
    }
    have separate(
        memory((((state as (void *)) as (uint32 *)) + index)[0..1]),
        memory(*(((state as (void *)) as (uint32 *)) + 3u64))
    ) by {
        rewrite(index, 1u64);
        close();
    }
    step_until(statement(0).region(5).entry);
    mark before_write;
    have state.values[0] == old(state.values[0]) by close();
    have state.values[2] == old(state.values[2]) by close();
    have state.values[3] == old(state.values[3]) by close();
    step();
    have separate(statement(0).region(5).footprint, memory(*(((state as (void *)) as (uint32 *)) + 0u64))) by {
        close();
    }
    have state.values[0] == at(before_write, state.values[0]) by {
        preserve(memory(*(((state as (void *)) as (uint32 *)) + 0u64)), statement(0).region(5));
    }
    have state.values[0] == old(state.values[0]) by close();
    have separate(statement(0).region(5).footprint, memory(*(((state as (void *)) as (uint32 *)) + 2u64))) by {
        close();
    }
    have state.values[2] == at(before_write, state.values[2]) by {
        preserve(memory(*(((state as (void *)) as (uint32 *)) + 2u64)), statement(0).region(5));
    }
    have state.values[2] == old(state.values[2]) by close();
    have separate(statement(0).region(5).footprint, memory(*(((state as (void *)) as (uint32 *)) + 3u64))) by {
        close();
    }
    have state.values[3] == at(before_write, state.values[3]) by {
        preserve(memory(*(((state as (void *)) as (uint32 *)) + 3u64)), statement(0).region(5));
    }
    have state.values[3] == old(state.values[3]) by close();
    step_until(function.exit);
}
fn array_first(values: &[u32; 4]) -> u32 {
    views values[0..4];
    ensures result == old(values[0]);
}
fn borrowed_first(state: &Lanes) -> u32 {
    views state.values[0..4];
    ensures result == old(state.values[0]);
}
fn tuple_read(state: &Words, index: usize) -> u32 {
    requires index < 4u64;
    views state.0[0..4];
    ensures result == old(state.0[index]);
}
fn byte_read(state: &Bytes, index: usize) -> u8 {
    requires index < 7u64;
    views (state.bytes)[0..7];
    ensures result == old(state.bytes[index]);
}
fn slice_first(bytes: &[u8]) -> u8 {
    requires bytes.len() > 0u64;
    requires bytes.len() <= 2147483647u64;
    views bytes[0..bytes.len()];
    ensures result == old(bytes[0]);
}
fn borrowed_byte(state: &Bytes) -> u8 {
    views (state.bytes)[0..7];
    ensures result == old(state.bytes[0]);
}
fn empty_len(state: &Empty) -> usize {
    ensures result == 0u64;
}
