verifying "snapshots.rs";
fn computed_move(a: u32, b: u32) -> u32 {
    ensures result == b ^ 1u32;
} by { execute(); solve(); }
fn source_write(a: u32, b: u32) -> u32 {
    ensures result == a;
} by { execute(); solve(); }
fn target_write(a: u32, b: u32) -> u32 {
    ensures result == b;
} by { execute(); solve(); }
fn replacement(a: u32, b: u32) -> u32 {
    ensures result == b;
} by { execute(); solve(); }
fn neighbors(a: u32, b: u32) -> u32 {
    ensures result == 28u32;
} by { execute(); solve(); }
fn sparse(a: u32, b: u32) -> u32 {
    ensures result == b;
} by { execute(); solve(); }
fn signed(a: i32, b: i32) -> i32 {
    ensures result == b;
} by { execute(); solve(); }
fn bytes(a: u8, b: u8) -> u8 {
    ensures result == b;
} by { execute(); solve(); }
