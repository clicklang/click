verifying "bindings.rs";

fn program_bindings::count(n: u32) -> u32 {
    requires n <= 1000u32;
    ensures result == n;
} by {
    step_until(loop(0));
    loop {
        decreases n - rust(iterations);
        invariant rust(iterations) <= n;
        invariant rust(iterations) == iterations;
    }
    have loop(0).iterations == n by { solve(); }
}
