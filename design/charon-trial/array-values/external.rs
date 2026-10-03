pub fn copy_small(target: &mut [u32; 8], source: &[u32; 8]) { *target = *source; }
pub fn fill_small(target: &mut [u32; 8], value: u32) { *target = [value; 8]; }
pub fn copy_medium(target: &mut [u32; 1024], source: &[u32; 1024]) { *target = *source; }
pub fn fill_medium(target: &mut [u32; 1024], value: u32) { *target = [value; 1024]; }
pub fn copy_million(target: &mut [u32; 1000000], source: &[u32; 1000000]) { *target = *source; }
pub fn fill_million(target: &mut [u32; 1000000], value: u32) { *target = [value; 1000000]; }
pub fn independent(source: &mut [i32; 2]) -> i32 { let saved = *source; source[0] = 99; saved[0] }
pub fn bytes(target: &mut [u8; 2], source: &[u8; 2]) { *target = *source; }
pub fn empty(target: &mut [u32; 0], source: &[u32; 0]) { *target = *source; }
