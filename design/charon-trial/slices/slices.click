verifying "slices.rs";
fn length(bytes: &[u8]) -> usize {
    ensures result == bytes.len();
} by { execute(); simp(); }
fn read(bytes: &[u8], index: usize) -> u8 {
    requires bytes.len() <= 2147483647u64;
    requires index < bytes.len();
    views bytes[0..bytes.len()];
    ensures result == old(bytes[index]);
} by { execute(); simp(); }
fn write(bytes: &mut [u8], index: usize, value: u8) {
    requires bytes.len() <= 2147483647u64;
    requires index < bytes.len();
    owns bytes[0..bytes.len()];
    ensures bytes[index] == value;
} by { execute(); simp(); }
fn alias(bytes: &mut [u8], index: usize) -> u8 {
    requires bytes.len() <= 2147483647u64;
    requires index < bytes.len();
    owns bytes[0..bytes.len()];
    ensures result == old(bytes[index]);
} by { execute(); simp(); }

fn write_read(bytes: &mut [u8], index: usize, value: u8) -> u8 {
    requires bytes.len() <= 2147483647u64;
    requires index < bytes.len();
    owns bytes[0..bytes.len()];
    ensures result == value;
    ensures bytes[index] == value;
} by { execute(); simp(); }

void Guard_drop(struct Guard* self) {
    requires separate(memory(*self), memory(self->slot[0..1]));
    owns self->slot;
    owns self->saved;
    owns self->slot[0..1];
    ensures self->slot == old(self->slot);
    ensures self->saved == old(self->saved);
    ensures self->slot[0] == old(self->saved);
} by { execute(); simp(); }

fn guarded_read(value: &mut i32, bytes: &[u8], index: usize) -> u32 {
    requires bytes.len() <= 2147483647u64;
    requires index < bytes.len();
    requires separate(memory(value[0..1]), memory(bytes[0..bytes.len()]));
    owns value[0..1];
    views bytes[0..bytes.len()];
    ensures result == old((uint32)bytes[index]);
    ensures value[0] == old(value[0]);
} by {
    execute();
    have index <= 2147483647u64 by { simp() using { index < bytes.len(); bytes.len() <= 2147483647u64; } }
    have 0 <= (int32)(uint32)index by { simp() using { index <= 2147483647u64; } }
    have ((int32)(uint32)index) < (int32)(uint32)bytes.len() by { simp() using { index < bytes.len(); bytes.len() <= 2147483647u64; } }
    simp();
}
