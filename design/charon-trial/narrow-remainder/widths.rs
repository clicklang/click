pub fn parity_u8(x: u8) -> u8 { if x % 2 == 0 { 1 } else { 0 } }
pub fn even_u8(x: u8) { assert!(x % 2 == 0); }
pub fn parity_u16(x: u16) -> u16 { if x % 2 == 0 { 1 } else { 0 } }
pub fn even_u16(x: u16) { assert!(x % 2 == 0); }
pub fn parity_u32(x: u32) -> u32 { if x % 2 == 0 { 1 } else { 0 } }
pub fn even_u32(x: u32) { assert!(x % 2 == 0); }
pub fn remainder_u8(x: u8, y: u8) -> u8 { x % y }
pub fn remainder_u16(x: u16, y: u16) -> u16 { x % y }
