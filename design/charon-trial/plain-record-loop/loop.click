verifying "loop.rs";
int32 packet_walk(int32 n) {
    requires 0 <= n and n <= 1000;
    ensures result == n;
} by {
    execute_until(loop(0));
    loop {
        decreases n - i;
        invariant 0 <= i and i <= n;
        invariant sum == i;
    }
    execute(); simp();
}
