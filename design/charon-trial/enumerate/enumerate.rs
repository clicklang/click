pub fn last_index(bytes: &[u8]) -> usize {
    let mut last = 0;
    for (i, &_byte) in bytes.iter().enumerate() {
        last = i;
    }
    last
}

pub fn last_pair(words: &[u16]) -> u32 {
    let mut index = 0;
    let mut value = 0;
    for (i, word) in words.iter().enumerate() {
        index = i;
        value = *word as u32;
    }
    if index < words.len() {
        value
    } else {
        0
    }
}
