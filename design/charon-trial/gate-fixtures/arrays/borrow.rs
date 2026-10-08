pub fn read(bytes: &[u8; 4], index: usize) -> u8 {
    bytes[index]
}

pub fn write(words: &mut [u32; 3], index: usize, value: u32) {
    let child = &mut words[index];
    *child = value;
}

pub fn signed(values: &[i32; 2], index: usize) -> i32 {
    (*values)[index]
}

pub fn length(words: &[u32; 1 + 2]) -> usize {
    words.len()
}

pub fn empty(bytes: &[u8; 0]) -> usize {
    bytes.len()
}

pub fn first(bytes: &[u8; 4]) -> u8 {
    let alias = bytes;
    read(alias, 0)
}

pub fn update(words: &mut [u32; 3]) {
    let child = &mut *words;
    write(child, 1, 7);
    words[2] = 9;
}
