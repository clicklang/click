verifying "owned.rs";
fn construct(value: u32, index: usize) -> u32 {
    requires index < 4u64;
    ensures result == value;
} by { execute(); simp(); }
fn moved(value: u32, index: usize) -> u32 {
    requires index < 4u64;
    ensures result == value;
} by { execute(); simp(); }
fn reassigned(value: u32, replacement: u32) -> u32 {
    ensures result == replacement;
} by { execute(); simp(); }
fn neighboring_fields(value: u32, replacement: u32) -> u32 {
    ensures result == 28u32;
} by { execute(); simp(); }
fn extracted(value: u32, index: usize) -> u32 {
    requires index < 4u64;
    ensures result == value;
} by { execute(); simp(); }
fn snapshot(value: u32) -> u32 {
    ensures result == value;
} by { execute(); simp(); }
fn tuple_move(value: u32) -> u32 {
    ensures result == value;
} by { execute(); simp(); }
fn byte_move(value: u8) -> u8 {
    ensures result == value;
} by { execute(); simp(); }
fn empty_move(value: u8) -> u8 {
    ensures result == 31u8;
} by { execute(); simp(); }
