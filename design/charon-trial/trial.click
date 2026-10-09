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
    } by {
        execute();
        simp();
    }
}

fn increment(x: u16) -> u16 {
    requires x < 65535;
    ensures result == x + 1;
} by {
    execute();
    simp();
}

fn guarded_increment(x: u16, value: &mut i32, early: bool) -> u16 {
    requires x < 65535;
    owns value[0..1];
    ensures result == x + 1;
    ensures value[0] == old(value[0]);
} by {
    execute();
    simp();
}
