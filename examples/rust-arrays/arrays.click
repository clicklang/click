verifying "arrays.rs";

fn read(bytes: &[u8; 4], index: usize) -> u8 {
    requires index < 4u64;
    views bytes[0..4];
    ensures result == bytes[index];
} by { execute(); simp(); }

fn write(words: &mut [u32; 3], index: usize, value: u32) {
    requires index < 3u64;
    owns words[index..index + 1];
    ensures words[index] == value;
} by { execute(); simp(); }

fn signed(values: &[i32; 2], index: usize) -> i32 {
    requires index < 2u64;
    views values[0..2];
    ensures result == values[index];
} by { execute(); simp(); }

fn length(words: &[u32; 1 + 2]) -> usize {
    ensures result == 3u64;
} by { execute(); simp(); }

fn empty(bytes: &[u8; 0]) -> usize {
    ensures result == 0u64;
} by { execute(); simp(); }

fn first(bytes: &[u8; 4]) -> u8 {
    views bytes[0..4];
    ensures result == bytes[0];
} by { execute(); simp(); }

fn update(words: &mut [u32; 3]) {
    owns words[0..3];
    ensures words[1] == 7u32;
    ensures words[2] == 9u32;
    ensures words[0] == old(words[0]);
} by { execute(); simp(); }
