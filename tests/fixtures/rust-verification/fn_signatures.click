verifying "borrow.rs";

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
