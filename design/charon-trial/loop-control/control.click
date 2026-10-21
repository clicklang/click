verifying "control.rs";

// `break` and `continue` lower to C `break` and `continue`. A loop whose
// body breaks lowers to `while (1)` whose test exits by `break` too, so each
// exit runs its own path to the code after the loop.

fn scan(n: i32) -> i32 {
    requires n >= 0;
    ensures 0i32 <= result and result <= n;
} by {
    execute_until(loop(0));
    loop {
        decreases i;
        invariant 0i32 <= i and i <= n;
    }
    execute(); simp();
}

fn first_stop(n: i32, limit: i32) -> i32 {
    requires 0i32 <= n and 0i32 <= limit;
    ensures 0i32 <= result and result <= limit and result <= n;
} by {
    execute_until(loop(0));
    loop {
        decreases limit - i;
        invariant 0i32 <= i and i <= limit and i <= n;
    }
    execute(); simp();
}

fn count_evens(n: i32) -> i32 {
    requires n >= 0;
    ensures 0i32 <= result and result <= n;
} by {
    execute_until(loop(0));
    loop {
        decreases n - i;
        invariant 0i32 <= i and i <= n and 0i32 <= evens and evens <= i;
    }
    execute(); simp();
}

fn countdown(n: i16) -> i16 {
    requires n >= 0i16;
    ensures result == 0i16;
} by {
    execute_until(loop(0));
    loop {
        decreases i;
        invariant 0i16 <= i and i <= n;
    }
    execute(); simp();
}
