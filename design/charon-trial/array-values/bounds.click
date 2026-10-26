verifying "bounds.rs";
fn swap() -> u32 { ensures result == 5u32; } by { execute(); solve(); }
fn self_copy() -> u8 { ensures result == 5; } by { execute(); solve(); }
fn signed() -> i32 { ensures result == -3; } by { execute(); solve(); }
fn fill_small() -> u32 { ensures result == 7u32; } by { execute(); solve(); }
fn copy_small() -> u32 { ensures result == 7u32; } by { execute(); solve(); }
fn fill_medium() -> u32 { ensures result == 7u32; } by { execute(); solve(); }
fn copy_medium() -> u32 { ensures result == 7u32; } by { execute(); solve(); }
fn fill_million() -> u32 { ensures result == 7u32; } by { execute(); solve(); }
fn copy_million() -> u32 { ensures result == 7u32; } by { execute(); solve(); }
fn empty() -> usize { ensures result == 0u64; } by { execute(); solve(); }
