verifying "probe.rs";

fn multiply(x:u32, rhs:u32) -> u32 {
    requires rhs == 0u32 or x <= 4294967295u32 / rhs;
    ensures result == x * rhs;
} by {
    apply(click::integer::uint32_multiply_to_integer(x, rhs));
    step_until(function.exit);
}
