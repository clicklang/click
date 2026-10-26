verifying "bounds.rs";
fn swap() -> u32 { ensures result == 5u32; }
fn self_copy() -> u8 { ensures result == 5; }
fn signed() -> i32 { ensures result == -3; }
fn fill_small() -> u32 { ensures result == 7u32; }
fn copy_small() -> u32 { ensures result == 7u32; }
fn fill_medium() -> u32 { ensures result == 7u32; }
fn copy_medium() -> u32 { ensures result == 7u32; }
fn fill_million() -> u32 { ensures result == 7u32; }
fn copy_million() -> u32 { ensures result == 7u32; }
fn empty() -> usize { ensures result == 0u64; }
