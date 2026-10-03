pub fn swap() -> u32 { let mut words = [3u32, 5]; let child = &mut words; *child = [child[1], child[0]]; words[0] }
pub fn self_copy() -> u8 { let mut words = [3u8, 5]; let child = &mut words; *child = *child; words[1] }
pub fn signed() -> i32 { let mut words = [0i32; 2]; let child = &mut words; *child = [-3, 7]; words[0] }
pub fn fill_small() -> u32 { let mut words = [0u32; 8]; let child = &mut words; *child = [7; 8]; words[7] }
pub fn copy_small() -> u32 { let mut source = [7u32; 8]; let mut target = [0u32; 8]; let child = &mut target; *child = source; source[7] = 9; target[7] }
pub fn fill_medium() -> u32 { let mut words = [0u32; 1024]; let child = &mut words; *child = [7; 1024]; words[1023] }
pub fn copy_medium() -> u32 { let mut source = [7u32; 1024]; let mut target = [0u32; 1024]; let child = &mut target; *child = source; source[1023] = 9; target[1023] }
pub fn fill_million() -> u32 { let mut words = [0u32; 1000000]; let child = &mut words; *child = [7; 1000000]; words[999999] }
pub fn copy_million() -> u32 { let mut source = [7u32; 1000000]; let mut target = [0u32; 1000000]; let child = &mut target; *child = source; source[999999] = 9; target[999999] }
pub fn empty() -> usize { let mut words: [u8;0] = []; let child = &mut words; *child = *child; words.len() }
