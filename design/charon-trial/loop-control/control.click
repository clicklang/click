verifying "control.rs";

// `break` and `continue` lower to C `break` and `continue`. A loop whose
// body breaks lowers to `while (1)` whose test exits by `break` too, so each
// exit runs its own path to the code after the loop.

fn scan(n: i32) -> i32 {
    requires n >= 0;
    ensures 0i32 <= result and result <= n;
} by {
    step_until(loop(0));
    loop {
        decreases i;
        invariant 0i32 <= i and i <= n;
    }
}

fn first_stop(n: i32, limit: i32) -> i32 {
    requires 0i32 <= n and 0i32 <= limit;
    ensures 0i32 <= result and result <= limit and result <= n;
} by {
    step_until(loop(0));
    loop {
        decreases limit - i;
        invariant 0i32 <= i and i <= limit and i <= n;
    }
}

fn count_evens(n: i32) -> i32 {
    requires n >= 0;
    ensures 0i32 <= result and result <= n;
} by {
    step_until(loop(0));
    loop {
        decreases n - i;
        invariant 0i32 <= i and i <= n and 0i32 <= evens and evens <= i;
    }
}

fn countdown(n: i16) -> i16 {
    requires n >= 0i16;
    ensures result == 0i16;
} by {
    step_until(loop(0));
    loop {
        decreases i;
        invariant 0i16 <= i and i <= n;
    }
}

fn count_to(n: u32) -> u32 {
    ensures result == n;
} by {
    step_until(loop(0));
    loop {
        decreases n - i;
        invariant i <= n;
    }
}

fn countdown_wide(n: i64) -> i64 {
    requires n >= 0i64;
    ensures result == 0i64;
} by {
    step_until(loop(0));
    loop {
        decreases i;
        invariant 0i64 <= i and i <= n;
    }
}

fn countdown_unsigned(n: u64) -> u64 {
    ensures result == 0u64;
} by {
    step_until(loop(0));
    loop {
        decreases i;
        invariant i <= n;
    }
}
