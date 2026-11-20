verifying "iteration.rs";
fn borrowed(words: &[u32; 4]) -> u32 {
    views words[0..4];
    ensures result == 4u32;
    ensures forall (k: int32) { 0 <= k and k < 4 implies words[k] == old(words[k]) };
}
fn moved(a: u32, b: u32) -> u32 {
    ensures result == (a ^ b);
}
fn bytes(a: u8, b: u8) -> u8 {
    ensures result == ((b ^ (a & 255)) & 255);
}
fn explicit(words: &[u32; 4]) -> u32 {
    views words[0..4];
    ensures result == 4u32;
}
fn local(a: u32, b: u32) -> u32 {
    ensures result == (a ^ b ^ 3u32 ^ 4u32);
}
fn empty() -> u32 {
    ensures result == 0u32;
}
fn ordered(a: u32, b: u32) -> u32 {
    ensures result == ((a << 1u32) ^ b);
}
fn shadowed(a: u32) -> u32 {
    ensures result == (a & 7u32) + 1u32;
} by {
    // The second `let x` takes the name from where its storage starts; the
    // first is the `x` statement 0 declares.
    step_until(assignment(x, 1).entry);
    have shadowed.statement(0).local(x) == (a & 7u32);
    have to_integer(a & 7u32) <= 7;
    step();
    have x == (a & 7u32) + 1u32;
}

fn signed(words: &[i32; 4]) -> i32 {
    views words[0..4];
    ensures result == old(words[0]);
    ensures words[3] == old(words[3]);
}
