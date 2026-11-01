verifying "widths.rs";
fn parity_u8(x: u8) -> u8 { requires x % 2u8 == 0u8; ensures result == 1u8; }
fn even_u8(x: u8) { requires x % 2u8 == 0u8; ensures true; }
fn parity_u16(x: u16) -> u16 { requires x % 2u16 == 0u16; ensures result == 1u16; }
fn even_u16(x: u16) { requires x % 2u16 == 0u16; ensures true; }
fn parity_u32(x: u32) -> u32 { requires x % 2u32 == 0u32; ensures result == 1u32; }
fn even_u32(x: u32) { requires x % 2u32 == 0u32; ensures true; }
fn remainder_u8(x: u8, y: u8) -> u8 { requires y != 0u8; ensures result == x % y; }
fn remainder_u16(x: u16, y: u16) -> u16 { requires y != 0u16; ensures result == x % y; }
