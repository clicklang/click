verifying "arithmetic.rs";

uint32 add_byte(uint32 sum, uint8 byte) {
    requires sum <= 4294967040u32;
    ensures result == sum + (uint32)byte;
} by { execute(); simp(); }

uint32 times_three(uint32 value) {
    requires value <= 1431655765u32;
    ensures result == value * 3u32;
} by { execute(); simp(); }

uint32 reduce(uint32 value) {
    ensures result == value % 65521u32;
} by { execute(); simp(); }

uint32 pack(uint32 low, uint32 high) {
    ensures result == ((high << 16) | low);
} by { execute(); simp(); }

uint8 low_byte(uint32 value) {
    ensures ((uint32)result) == (value & 255u32);
} by { execute(); simp(); }

bool high_bit(uint32 value) {
    ensures result == (if value > 2147483647u32 { 1 } else { 0 });
} by {
    if value > 2147483647u32 { execute(); simp(); }
    else { execute(); simp(); }
}

uint8 shifted_byte(uint8 value, uint32 count) {
    requires count < 8u32;
    ensures ((uint32)result) == (((uint32)value << count) & 255u32);
} by { execute(); simp(); }

uint8 discarded_shift_bits() {
    ensures result == 0;
} by { execute(); simp(); }
