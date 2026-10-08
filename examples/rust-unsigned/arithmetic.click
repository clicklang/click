verifying "arithmetic.rs";

fn add_byte(sum: u32, byte: u8) -> u32 {
    requires sum <= 4294967040u32;
    ensures result == sum + byte as u32;
} by { execute(); simp(); }

fn times_three(value: u32) -> u32 {
    requires value <= 1431655765u32;
    ensures result == value * 3u32;
} by { execute(); simp(); }

fn reduce(value: u32) -> u32 {
    ensures result == value % 65521u32;
} by { execute(); simp(); }

fn pack(low: u32, high: u32) -> u32 {
    ensures result == ((high << 16) | low);
} by { execute(); simp(); }

fn low_byte(value: u32) -> u8 {
    ensures (result as u32) == (value & 255u32);
} by { execute(); simp(); }

fn high_bit(value: u32) -> bool {
    ensures result == (if value > 2147483647u32 { 1 } else { 0 });
} by {
    if value > 2147483647u32 { execute(); simp(); }
    else { execute(); simp(); }
}

fn shifted_byte(value: u8, count: u32) -> u8 {
    requires count < 8u32;
    ensures (result as u32) == ((value as u32 << count) & 255u32);
} by { execute(); simp(); }

fn discarded_shift_bits() -> u8 {
    ensures result == 0;
} by { execute(); simp(); }
