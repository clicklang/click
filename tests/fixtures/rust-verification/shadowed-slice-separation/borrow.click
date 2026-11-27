verifying "side.rs";

fn add(q: &mut u32, delta: u32) {
    owns *q;
    requires to_integer(*q) + to_integer(delta) <= 4294967295;
    ensures *q == old(*q) + delta;
} by {
    step_until(function.exit);
    close();
    close();
}

fn use_scalar(bytes: &[u8], initial: u32, delta: u32) -> u32 {
    views *bytes;
    requires to_integer(initial) + to_integer(delta) <= 4294967295;
    ensures result == initial + delta;
} by {
    step_until(function.exit);
    close();
}
