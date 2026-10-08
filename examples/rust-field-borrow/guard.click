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

fn cleanup(value: &mut i32) {
    owns *value;
    ensures *value == 42;
} by {
    execute();
    simp();
}
