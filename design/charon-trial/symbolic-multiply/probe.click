verifying "probe.rs";

fn multiply(x:u32, rhs:u32) -> u32 {
    requires rhs == 0u32 or x <= 4294967295u32 / rhs;
    ensures result == x * rhs;
} by { execute(); simp(); }
