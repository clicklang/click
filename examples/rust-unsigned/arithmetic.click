verifying "arithmetic.rs";

fn add_byte(sum: u32, byte: u8) -> u32 {
    requires sum <= 4294967040u32;
    ensures result == sum + byte as u32;
} by { execute(); auto(); }

fn times_three(value: u32) -> u32 {
    requires value <= 1431655765u32;
    ensures result == value * 3u32;
} by { execute(); apply(uint32_multiply_to_integer(value, 3u32)); auto(); }

fn reduce(value: u32) -> u32 {
    ensures result == value % 65521u32;
} by { execute(); auto(); }

fn pack(low: u32, high: u32) -> u32 {
    ensures result == ((high << 16) | low);
} by { execute(); auto(); }

fn low_byte(value: u32) -> u8 {
    ensures (result as u32) == (value & 255u32);
} by { execute(); auto(); }

fn high_bit(value: u32) -> bool {
    ensures result == (value > 2147483647u32);
} by {
    if value > 2147483647u32 { execute(); auto(); }
    else { execute(); auto(); }
}

fn shifted_byte(value: u8, count: u32) -> u8 {
    requires count < 8u32;
    ensures (result as u32) == ((value as u32 << count) & 255u32);
} by { execute(); auto(); }

fn discarded_shift_bits() -> u8 {
    ensures result == 0;
} by { execute(); auto(); }

import click::integer;
arithmetic "integer";
