pub fn add_byte(sum: u32, byte: u8) -> u32 {
    sum + byte as u32
}

pub fn times_three(value: u32) -> u32 {
    value * 3
}

pub fn reduce(value: u32) -> u32 {
    value % 65521
}

pub fn pack(low: u32, high: u32) -> u32 {
    (high << 16) | low
}

pub fn low_byte(value: u32) -> u8 {
    value as u8
}

pub fn high_bit(value: u32) -> bool {
    value > 2147483647
}

pub fn shifted_byte(value: u8, count: u32) -> u8 {
    value << count
}

pub fn discarded_shift_bits() -> u8 {
    128u8 << 1
}
