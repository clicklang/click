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
    } by {
        execute();
        simp();
    }
}

fn restore(early: bool, value: &mut i32) -> i32 {
    owns *value;
    ensures result == (if early != 0 { 7 } else { 9 });
    ensures *value == old(*value);
} by {
    execute();
    simp();
}
