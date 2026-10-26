verifying "slices.rs";
fn length(bytes: &[u8]) -> usize {
    ensures result == bytes.len();
}
fn read(bytes: &[u8], index: usize) -> u8 {
    requires bytes.len() <= 2147483647u64;
    requires index < bytes.len();
    views bytes[0..bytes.len()];
    ensures result == old(bytes[index]);
}
fn write(bytes: &mut [u8], index: usize, value: u8) {
    requires bytes.len() <= 2147483647u64;
    requires index < bytes.len();
    owns bytes[0..bytes.len()];
    ensures bytes[index] == value;
}
fn alias(bytes: &mut [u8], index: usize) -> u8 {
    requires bytes.len() <= 2147483647u64;
    requires index < bytes.len();
    owns bytes[0..bytes.len()];
    ensures result == old(bytes[index]);
}

fn write_read(bytes: &mut [u8], index: usize, value: u8) -> u8 {
    requires bytes.len() <= 2147483647u64;
    requires index < bytes.len();
    owns bytes[0..bytes.len()];
    ensures result == value;
    ensures bytes[index] == value;
} by {
    step_until(function.exit);
    have result == bytes[index];
    solve();
}

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

fn guarded_read(value: &mut i32, bytes: &[u8], index: usize) -> u32 {
    requires bytes.len() <= 2147483647u64;
    requires index < bytes.len();
    requires separate(memory(value[0..1]), memory(bytes[0..bytes.len()]));
    owns value[0..1];
    views bytes[0..bytes.len()];
    ensures result == old(bytes[index] as uint32);
    ensures value[0] == old(value[0]);
} by {
    step_until(function.exit);
    have index <= 2147483647u64 by { solve() using { index < bytes.len(); bytes.len() <= 2147483647u64; }; }
    have 0 <= index as uint32 as int32 by { solve() using { index <= 2147483647u64; }; }
    have (index as uint32 as int32) < bytes.len() as uint32 as int32 by { solve() using { index < bytes.len(); bytes.len() <= 2147483647u64; }; }
    solve();
}
