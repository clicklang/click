verifying "external.rs";

fn copy_small(target: &mut [u32; 8], source: &[u32; 8]) {
    owns target[0..8];
    views source[0..8];
    ensures target[0] == old(source[0]);
    ensures target[7] == old(source[7]);
} by { execute(); simp(); }

fn fill_small(target: &mut [u32; 8], value: u32) {
    owns target[0..8];
    ensures target[0] == value;
    ensures target[7] == value;
} by { execute(); simp(); }

fn copy_medium(target: &mut [u32; 1024], source: &[u32; 1024]) {
    owns target[0..1024];
    views source[0..1024];
    ensures target[0] == old(source[0]);
    ensures target[1023] == old(source[1023]);
} by { execute(); simp(); }

fn fill_medium(target: &mut [u32; 1024], value: u32) {
    owns target[0..1024];
    ensures target[0] == value;
    ensures target[1023] == value;
} by { execute(); simp(); }

fn copy_million(target: &mut [u32; 1000000], source: &[u32; 1000000]) {
    owns target[0..1000000];
    views source[0..1000000];
    ensures target[0] == old(source[0]);
    ensures target[999999] == old(source[999999]);
} by { execute(); simp(); }

fn fill_million(target: &mut [u32; 1000000], value: u32) {
    owns target[0..1000000];
    ensures target[0] == value;
    ensures target[999999] == value;
} by { execute(); simp(); }

fn independent(source: &mut [i32; 2]) -> i32 { owns source[0..2]; ensures result == old(source[0]); ensures source[0] == 99; } by { execute(); simp(); }
fn bytes(target: &mut [u8; 2], source: &[u8; 2]) { owns target[0..2]; views source[0..2]; ensures target[0] == old(source[0]); ensures target[1] == old(source[1]); } by { execute(); simp(); }
fn empty(target: &mut [u32; 0], source: &[u32; 0]) { ensures 0u32 == 0u32; } by { execute(); simp(); }
