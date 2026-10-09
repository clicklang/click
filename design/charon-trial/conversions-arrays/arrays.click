verifying "arrays.rs";

impl Drop for Guard {
    fn drop(&mut self) {
        requires separate(memory(*self), memory(self.slot[0..1]));
        owns self.slot;
        owns self.saved;
        owns *self.slot;
        ensures self.slot == old(self.slot);
        ensures self.saved == old(self.saved);
        ensures *self.slot == old(self.saved);
    } by { execute(); simp(); }
}

fn guarded_array(value: &mut i32, x: u16) -> u32 {
    owns value[0..1];
    ensures result == x;
    ensures value[0] == old(value[0]);
} by { execute(); simp(); }

fn large_array() -> u8 {
    ensures result == 7;
} by { execute(); simp(); }

fn increment(value: &mut i32) -> u8 {
    requires value[0] < 2147483647;
    owns value[0..1];
    ensures result == 7;
    ensures value[0] == old(value[0]) + 1;
} by { execute(); simp(); }

fn empty_array(value: &mut i32) {
    requires value[0] < 2147483647;
    owns value[0..1];
    ensures value[0] == old(value[0]) + 1;
} by { execute(); simp(); }

fn explicit_array() -> u32 {
    ensures result == 9;
} by { execute(); simp(); }

fn cast_array(x: u32) -> u8 {
    requires x == 257;
    ensures result == 1;
} by { execute(); simp(); }
