pub fn count_to(n: u32) -> u32 {
    let mut total = 0;
    for _i in 0..n {
        total += 1;
    }
    total
}

pub fn span(a: i32, b: i32) -> i32 {
    let mut count = 0;
    for _k in a..b {
        count += 1;
    }
    count
}

pub fn count_signed_wide(n: i64) -> i64 {
    let mut count = 0;
    for _i in 0..n {
        count += 1;
    }
    count
}

pub fn last_byte(bytes: &[u8]) -> u8 {
    let mut last = 0;
    for i in 0..bytes.len() {
        last = bytes[i];
    }
    last
}

pub fn grid(n: u32, m: u32) -> u32 {
    let mut cells = 0;
    for _i in 0..n {
        for _j in 0..m {
            cells += 1;
        }
    }
    cells
}
