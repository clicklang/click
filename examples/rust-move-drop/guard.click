verifying "guard.rs";

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

fn restore(early: bool, value: &mut i32) -> i32 {
    owns *value;
    ensures result == (if early { 7 } else { 9 });
    ensures *value == old(*value);
} by {
    step_until(statement(4).entry);
    if not early {
        step_until(call(Guard_drop, 0).entry);
        mark drop_normal;
        step() by {
            known();
        }
        have *moved.slot == at(drop_normal, moved.saved) by known();
        have moved.slot == at(drop_normal, moved.slot) by known();
        have at(drop_normal, moved.slot) == value by known();
        have moved.slot == value by {
            rewrite(moved.slot, at(drop_normal, moved.slot));
            known();
        }
        have *value == at(drop_normal, moved.saved) by {
            rewrite(value, moved.slot);
            known();
        }
        step_until(function.exit);
        have result == (if early == true { 7 } else { 9 }) by {
            known();
        }
        have at(drop_normal, moved.saved) == old(*value) by known();
        have *value == old(*value) by {
            rewrite(*value, at(drop_normal, moved.saved));
            known();
        }
    } else {
        step_until(call(Guard_drop, 1).entry);
        mark drop_early;
        step() by {
            known();
        }
        have *moved.slot == at(drop_early, moved.saved) by known();
        have moved.slot == at(drop_early, moved.slot) by known();
        have at(drop_early, moved.slot) == value by known();
        have moved.slot == value by {
            rewrite(moved.slot, at(drop_early, moved.slot));
            known();
        }
        have *value == at(drop_early, moved.saved) by {
            rewrite(value, moved.slot);
            known();
        }
        step_until(function.exit);
        have result == (if early == true { 7 } else { 9 }) by {
            known();
        }
        have at(drop_early, moved.saved) == old(*value) by known();
        have *value == old(*value) by {
            rewrite(*value, at(drop_early, moved.saved));
            known();
        }
    }
}
