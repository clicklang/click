verifying "loops.rs";

int32 count(int32 n) {
    requires n >= 0;
    ensures result == n;
} by {
    execute_until(assignment(i, 0)); step();
    have i == 0 by { simp(); }
    execute_until(loop(0));
    loop {
        decreases n - i;
        invariant 0 <= i and i <= n;
    }
    execute(); simp();
}

int32 accumulate(int32 n, int32 value) {
    requires n >= 0;
    requires value == 1;
    ensures result == n;
} by {
    execute_until(assignment(i, 0)); step();
    have i == 0 by { simp(); }
    execute_until(loop(0));
    loop {
        decreases n - i;
        invariant 0 <= i and i <= n;
        invariant sum == i;
    }
    execute(); simp();
}

uint64 walk(const uint8* bytes, uint64 bytes_len) {
    requires bytes_len <= 2147483647u64;
    views bytes[0..(int32)bytes_len];
    ensures result == bytes_len;
} by {
    execute_until(assignment(i, 0)); step();
    have i == 0 by { simp(); }
    execute_until(loop(0));
    loop {
        decreases bytes_len - i;
        invariant i <= bytes_len;
    }
    execute(); simp();
}
