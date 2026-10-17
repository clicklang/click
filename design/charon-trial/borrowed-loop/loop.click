import click::machine_integer;

verifying "loop.rs";

impl Drop for Guard {
    fn drop(&mut self) {
        requires separate(memory(*self), memory(self.slot[0..1]));
        owns self.slot;
        owns self.saved;
        owns *self.slot;
        ensures self.slot == old(self.slot);
        ensures self.saved == old(self.saved);
        ensures *self.slot == old(self.saved);
    } by {
        execute(); simp();
    }
}

fn guarded_walk(value: &mut i32, n: i32) -> i32 {
    requires n >= 0;
    owns value[0..1];
    ensures result == n;
    ensures value[0] == old(value[0]);
} by {
    execute_until(loop(0));
    loop {
        decreases n - i;
        preserve by {
            apply(int32_nonnegative_subtract_within_value_is_defined(n, i)) using {
                0 <= i;
                i <= n;
            };
            have 0 < n - i by { arithmetic() using { 0 <= i; i < n; }; }
            apply(int32_positive_predecessor_is_nonnegative(n - i)) using { 0 < n - i; };
            apply(int32_positive_predecessor_strictly_decreases(n - i)) using { 0 < n - i; };
            execute_until(back_edge());
            close_invariants() by simp();
        }
        owns value[0..1];
        views guard.slot;
        views guard.saved;
        invariant 0 <= i and i <= n;
        invariant separate(memory(guard.slot), memory(value[0..1]));
        invariant separate(memory(guard.saved), memory(value[0..1]));
        invariant guard.slot == value;
        invariant guard.saved == old(value[0]);
    }
    execute(); simp();
}

fn final_header(n: i32) -> i32 {
    requires n >= 0;
    ensures result == n;
} by {
    execute_until(loop(0));
    loop {
        decreases n - i;
        preserve by {
            apply(int32_nonnegative_subtract_within_value_is_defined(n, i)) using {
                0 <= i;
                i <= n;
            };
            have 0 < n - i by { arithmetic() using { 0 <= i; i < n; }; }
            apply(int32_positive_predecessor_is_nonnegative(n - i)) using { 0 < n - i; };
            apply(int32_positive_predecessor_strictly_decreases(n - i)) using { 0 < n - i; };
            execute_until(back_edge());
            close_invariants() by simp();
        }
        invariant 0 <= i and i <= n;
    }
    execute(); simp();
}
