verifying "probe.rs";

uint32 multiply(uint32 x, uint32 rhs) {
    requires rhs == 0u32 or x <= 4294967295u32 / rhs;
    ensures result == x * rhs;
} by { execute(); simp(); }
