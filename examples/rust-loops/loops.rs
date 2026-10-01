pub fn count(n: i32) -> i32 {
    let mut i = 0;
    while i < n {
        i += 1;
    }
    i
}

pub fn accumulate(n: i32, value: i32) -> i32 {
    let mut i = 0;
    let mut sum = 0;
    while i < n {
        sum += value;
        i += 1;
    }
    sum
}

pub fn walk(bytes: &[u8]) -> usize {
    let mut i = 0usize;
    while i < bytes.len() {
        let _byte = bytes[i];
        i += 1;
    }
    i
}
