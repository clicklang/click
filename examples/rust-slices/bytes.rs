pub fn length(bytes: &[u8]) -> usize {
    bytes.len()
}

pub fn read(bytes: &[u8], index: usize) -> u8 {
    bytes[index]
}

pub fn write(bytes: &mut [u8], index: usize, value: u8) {
    bytes[index] = value;
}

pub fn first(bytes: &[u8]) -> u8 {
    let alias = bytes;
    read(alias, 0)
}

pub fn increment_first(bytes: &mut [u8]) {
    let child = &mut *bytes;
    let value = child[0];
    child[0] = value + 1;
}

pub fn empty(bytes: &[u8]) -> bool {
    bytes.len() == 0
}
