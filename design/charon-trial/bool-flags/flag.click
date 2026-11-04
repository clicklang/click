verifying "flag.rs";

fn bool_flags::scan(n: u32) -> u32 {
    ensures result <= n;
} by {
    step_until(loop(0));
    loop {
        decreases n - t;
        invariant t <= n;
        invariant found implies t == 8u32;
    }
}
