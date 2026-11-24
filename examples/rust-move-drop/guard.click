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
            close();
        }
        have *moved.slot == at(drop_normal, moved.saved) by close();
        have moved.slot == at(drop_normal, moved.slot) by close();
        have at(drop_normal, moved.slot) == value by close();
        have moved.slot == value by {
            rewrite(moved.slot, at(drop_normal, moved.slot));
            close();
        }
        have *value == at(drop_normal, moved.saved) by {
            rewrite(value, moved.slot);
            close();
        }
        step_until(function.exit);
        have result == (if early == true { 7 } else { 9 }) by {
            close();
        }
        have at(drop_normal, moved.saved) == old(*value) by close();
        have *value == old(*value) by {
            rewrite(*value, at(drop_normal, moved.saved));
            close();
        }
    } else {
        step_until(call(Guard_drop, 1).entry);
        mark drop_early;
        step() by {
            close();
        }
        have *moved.slot == at(drop_early, moved.saved) by close();
        have moved.slot == at(drop_early, moved.slot) by close();
        have at(drop_early, moved.slot) == value by close();
        have moved.slot == value by {
            rewrite(moved.slot, at(drop_early, moved.slot));
            close();
        }
        have *value == at(drop_early, moved.saved) by {
            rewrite(value, moved.slot);
            close();
        }
        step_until(function.exit);
        have result == (if early == true { 7 } else { 9 }) by {
            close();
        }
        have at(drop_early, moved.saved) == old(*value) by close();
        have *value == old(*value) by {
            rewrite(*value, at(drop_early, moved.saved));
            close();
        }
    }
}
