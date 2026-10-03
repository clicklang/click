pub fn borrowed(words: &[u32; 4]) -> u32 {
    let mut count = 0;
    for _word in words {
        count += 1;
    }
    count
}
pub fn explicit(words: &[u32; 4]) -> u32 {
    let mut count = 0;
    for _word in words.iter() {
        count += 1;
    }
    count
}
pub fn local(a: u32, b: u32) -> u32 {
    let words = [a, b, 3, 4];
    let mut result = 0;
    for word in &words {
        result ^= *word;
    }
    result
}
pub fn empty() -> u32 {
    let words: [u32; 0] = [];
    let mut count = 0;
    for _word in &words {
        count += 1;
    }
    count
}
pub fn ordered(a: u32, b: u32) -> u32 {
    let words = [a, b];
    let mut iter = words.iter();
    let first = match iter.next() { Some(word) => *word, None => 0 };
    let second = match iter.next() { Some(word) => *word, None => 0 };
    (first << 1) ^ second
}

pub fn moved(a: u32, b: u32) -> u32 {
    let words = [a, b];
    let mut initial = words.iter();
    let first = match initial.next() { Some(word) => *word, None => 0 };
    let mut remaining = initial;
    let second = match remaining.next() { Some(word) => *word, None => 0 };
    let _end = match remaining.next() { Some(_) => false, None => true };
    let _again = match remaining.next() { Some(_) => false, None => true };
    first ^ second
}

pub fn bytes(a: u8, b: u8) -> u8 {
    let words = [a, b];
    let mut result = 0;
    for word in &words { result ^= *word; }
    result
}

pub fn signed(words: &[i32; 4]) -> i32 {
    let mut iter = words.iter();
    match iter.next() { Some(word) => *word, None => 0 }
}
