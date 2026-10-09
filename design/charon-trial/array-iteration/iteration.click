verifying "iteration.rs";
fn borrowed(words: &[u32; 4]) -> u32 {
    views words[0..4];
    ensures result == 4u32;
    ensures forall (k: int32) { 0 <= k and k < 4 implies words[k] == old(words[k]) };
} by { execute(); simp(); }
fn moved(a: u32, b: u32) -> u32 {
    ensures result == (a ^ b);
} by { execute(); simp(); }
fn bytes(a: u8, b: u8) -> u8 {
    ensures result == ((b ^ (a & 255)) & 255);
} by { execute(); simp(); }
fn explicit(words: &[u32; 4]) -> u32 {
    views words[0..4];
    ensures result == 4u32;
} by { execute(); simp(); }
fn local(a: u32, b: u32) -> u32 {
    ensures result == (a ^ b ^ 3u32 ^ 4u32);
} by { execute(); simp(); }
fn empty() -> u32 {
    ensures result == 0u32;
} by { execute(); simp(); }
fn ordered(a: u32, b: u32) -> u32 {
    ensures result == ((a << 1u32) ^ b);
} by { execute(); simp(); }

fn signed(words: &[i32; 4]) -> i32 {
    views words[0..4];
    ensures result == old(words[0]);
    ensures words[3] == old(words[3]);
} by { execute(); simp(); }
