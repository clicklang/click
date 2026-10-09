verifying "arithmetic.rs";

fn add_byte(sum: u32, byte: u8) -> u32 {
    requires sum <= 4294967040u32;
    ensures result == sum + (uint32)byte;
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
    ensures ((uint32)result) == (value & 255u32);
} by { execute(); simp(); }

fn high_bit(value: u32) -> bool {
    ensures result == (if value > 2147483647u32 { 1 } else { 0 });
} by {
    if value > 2147483647u32 { execute(); simp(); }
    else { execute(); simp(); }
}

fn shifted_byte(value: u8, count: u32) -> u8 {
    requires count < 8u32;
    ensures ((uint32)result) == (((uint32)value << count) & 255u32);
} by { execute(); simp(); }

fn discarded_shift_bits() -> u8 {
    ensures result == 0;
} by { execute(); simp(); }

fn quotient_byte(value: u8, divisor: u8) -> u8 {
    requires divisor != 0;
    ensures ((uint32)result) == (uint32)value / (uint32)divisor;
} by { execute(); simp(); }
fn quotient_word(value: u16, divisor: u16) -> u16 {
    requires divisor != 0;
    ensures ((uint32)result) == (uint32)value / (uint32)divisor;
} by { execute(); simp(); }
fn quotient(value: u32, divisor: u32) -> u32 {
    requires divisor != 0u32;
    ensures result == value / divisor;
} by { execute(); simp(); }
fn remainder_word(value: u16, divisor: u16) -> u16 {
    requires divisor != 0;
    ensures ((uint32)result) == (uint32)value % (uint32)divisor;
} by { execute(); simp(); }
fn wide_quotient(value: usize, divisor: usize) -> usize {
    requires divisor != 0u64;
    ensures result == value / divisor;
} by { execute(); simp(); }
fn wide_remainder(value: usize, divisor: usize) -> usize {
    requires divisor != 0u64;
    ensures result == value % divisor;
} by { execute(); simp(); }
fn wide_left(value: usize, count: usize) -> usize {
    requires count < 64u64;
    ensures result == value << count;
} by { execute(); simp(); }
fn wide_right(value: usize, count: usize) -> usize {
    requires count < 64u64;
    ensures result == value >> count;
} by { execute(); simp(); }
fn word_right(value: u16, count: usize) -> u16 {
    requires count < 16u64;
    ensures ((uint32)result) == (((uint32)value >> count) & 65535u32);
} by { execute(); simp(); }
fn signed_count(value: u32, count: i32) -> u32 {
    requires 0 <= count and count < 32;
    ensures result == value << count;
} by { execute(); simp(); }
fn invert_byte(value: u8) -> u8 { ensures ((uint32)result) == ((~(uint32)value) & 255u32); } by { execute(); simp(); }
fn invert_word(value: u16) -> u16 { ensures ((uint32)result) == ((~(uint32)value) & 65535u32); } by { execute(); simp(); }
fn invert(value: u32) -> u32 { ensures result == ~value; } by { execute(); simp(); }
fn wide_invert(value: usize) -> usize { ensures result == ~value; } by { execute(); simp(); }
fn masked(value: u32, mask: u32) -> u32 { ensures result == ((value & mask) ^ ~value); } by { execute(); simp(); }
fn conditional_divide(value: u32, divisor: u32, skip: bool) -> u32 {
    requires skip != 0 or divisor != 0u32;
    ensures skip != 0 implies result == 0u32;
    ensures skip == 0 implies result == value / divisor;
} by { if skip != 0 { execute(); simp(); } else { have divisor != 0u32 by { cases { skip != 0 => { contradiction(skip != 0); } divisor != 0u32 => { assumption(); } } } execute(); simp(); } }
