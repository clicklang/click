import click::integer;

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
    }
}

fn guarded_walk(value: &mut i32, n: i32) -> i32 {
    requires n >= 0;
    owns value[0..1];
    ensures result == n;
    ensures value[0] == old(value[0]);
} by {
    step_until(loop(0).entry);
    loop {
        decreases n - i;
        maintain by {
            apply(integer::int32_nonnegative_subtract_within_value_is_defined(n, i));
            have 0 < n - i by { close() using { 0 <= i; i < n; }; }
            apply(integer::int32_positive_predecessor_is_nonnegative(n - i));
            apply(integer::int32_positive_predecessor_strictly_decreases(n - i));
            step_until(region(31).entry);
            have guard.slot == value by { close(); }
            have guard.saved == old(value[0]) by { close(); }
            have slot == value by { close(); }
            have separate(memory(*slot), memory(guard.slot)) by {
                rewrite(slot, value);
                close();
            }
            have separate(memory(*slot), memory(guard.saved)) by {
                rewrite(slot, value);
                close();
            }
            mark before_write;
            step();
            have separate(region(31).footprint, memory(guard.slot)) by {
                normalize() using { at(before_write, separate(memory(*slot), memory(guard.slot))); };
            }
            have separate(region(31).footprint, memory(guard.saved)) by {
                normalize() using { at(before_write, separate(memory(*slot), memory(guard.saved))); };
            }
            have guard.slot == at(before_write, guard.slot) by {
                preserve(memory(guard.slot), region(31));
            }
            have guard.saved == at(before_write, guard.saved) by close();
            have guard.slot == value by {
                rewrite(guard.slot, at(before_write, guard.slot));
                close();
            }
            have guard.saved == old(value[0]) by {
                rewrite(guard.saved, at(before_write, guard.saved));
                close();
            }
            step_until(loop.back_edge);
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
}

fn final_header(n: i32) -> i32 {
    requires n >= 0;
    ensures result == n;
} by {
    step_until(loop(0).entry);
    loop {
        decreases n - i;
        maintain by {
            apply(integer::int32_nonnegative_subtract_within_value_is_defined(n, i));
            have 0 < n - i by { close() using { 0 <= i; i < n; }; }
            apply(integer::int32_positive_predecessor_is_nonnegative(n - i));
            apply(integer::int32_positive_predecessor_strictly_decreases(n - i));
            step_until(loop.back_edge);
        }
        invariant 0 <= i and i <= n;
    }
}
