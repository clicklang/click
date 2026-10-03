verifying "bounds.rs";
uint32 swap() { ensures result == 5u32; } by { execute(); simp(); }
uint8 self_copy() { ensures result == 5; } by { execute(); simp(); }
int32 signed() { ensures result == -3; } by { execute(); simp(); }
uint32 fill_small() { ensures result == 7u32; } by { execute(); simp(); }
uint32 copy_small() { ensures result == 7u32; } by { execute(); simp(); }
uint32 fill_medium() { ensures result == 7u32; } by { execute(); simp(); }
uint32 copy_medium() { ensures result == 7u32; } by { execute(); simp(); }
uint32 fill_million() { ensures result == 7u32; } by { execute(); simp(); }
uint32 copy_million() { ensures result == 7u32; } by { execute(); simp(); }
uint64 empty() { ensures result == 0u64; } by { execute(); simp(); }
