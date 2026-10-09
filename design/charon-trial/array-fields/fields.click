verifying "fields.rs";
fn read(state: &Lanes, index: usize) -> u32 {
    requires index < 4u64;
    views state->values[0..4];
    ensures result == old(state->values[index]);
} by { execute(); simp(); }
fn write(state: &mut Lanes, index: usize, value: u32) {
    requires index == 1u64;
    owns state->values[0..4];
    views state->marker;
    ensures state->values[index] == value;
    ensures state->values[0] == old(state->values[0]);
    ensures state->values[2] == old(state->values[2]);
    ensures state->values[3] == old(state->values[3]);
    ensures state->marker == old(state->marker);
} by {
    have ((int32)(uint32)index) == 1 by { rewrite(index == 1u64); simp(); }
    execute(); simp();
}
fn array_first(values: &[u32; 4]) -> u32 {
    views values[0..4];
    ensures result == old(values[0]);
} by { execute(); simp(); }
fn borrowed_first(state: &Lanes) -> u32 {
    views state->values[0..4];
    ensures result == old(state->values[0]);
} by { execute(); simp(); }
fn tuple_read(state: &Words, index: usize) -> u32 {
    requires index < 4u64;
    views state->_0[0..4];
    ensures result == old(state->_0[index]);
} by { execute(); simp(); }
fn byte_read(state: &Bytes, index: usize) -> u8 {
    requires index < 7u64;
    views (state->bytes)[0..7];
    ensures result == old(state->bytes[index]);
} by { execute(); simp(); }
fn slice_first(bytes: &[u8]) -> u8 {
    requires bytes.len() > 0u64;
    requires bytes.len() <= 2147483647u64;
    views bytes[0..bytes.len()];
    ensures result == old(bytes[0]);
} by { execute(); simp(); }
fn borrowed_byte(state: &Bytes) -> u8 {
    views (state->bytes)[0..7];
    ensures result == old(state->bytes[0]);
} by { execute(); simp(); }
fn empty_len(state: &Empty) -> usize {
    ensures result == 0u64;
} by { execute(); simp(); }
