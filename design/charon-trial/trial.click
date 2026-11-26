verifying "trial.rs";

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

fn increment(x: u16) -> u16 {
    requires x < 65535;
    ensures result == x + 1;
}

fn guarded_increment(x: u16, value: &mut i32, early: bool) -> u16 {
    requires x < 65535;
    owns value[0..1];
    ensures result == x + 1;
    ensures value[0] == old(value[0]);
} by {
    step_until(statement(4).entry);
    if early {
        step_until(call(Guard_drop, 1).entry);
        have guard.slot == value by { close(); }
        have guard.saved == old(value[0]) by { close(); }
        mark before_drop;
        step(Guard_drop);
        have guard.slot == value by { close(); }
        have guard.slot[0] == at(before_drop, guard.saved) by { close(); }
        have value[0] == at(before_drop, guard.saved) by {
            rewrite(value, guard.slot);
            close();
        }
        have value[0] == old(value[0]) by {
            rewrite(value[0], at(before_drop, guard.saved));
            close();
        }
        step_until(function.exit);
        close();
    } else {
        step_until(call(Guard_drop, 0).entry);
        have moved.slot == value by { close(); }
        have moved.saved == old(value[0]) by { close(); }
        mark before_drop;
        step(Guard_drop);
        have moved.slot == value by { close(); }
        have moved.slot[0] == at(before_drop, moved.saved) by { close(); }
        have value[0] == at(before_drop, moved.saved) by {
            rewrite(value, moved.slot);
            close();
        }
        have value[0] == old(value[0]) by {
            rewrite(value[0], at(before_drop, moved.saved));
            close();
        }
        step_until(function.exit);
        close();
    }
}
