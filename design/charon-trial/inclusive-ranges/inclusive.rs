pub fn count_through(n: u32) -> u32 {
    let mut total = 0;
    for _i in 0..=n {
        total += 1;
    }
    total
}

pub fn every_byte() -> u32 {
    let mut total = 0u32;
    for _b in 0u8..=255 {
        total += 1;
    }
    total
}
