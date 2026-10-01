pub struct Guard<'a> {
    pub slot: &'a mut i32,
    pub saved: i32,
}
impl Drop for Guard<'_> {
    fn drop(&mut self) {
        *self.slot = self.saved;
    }
}
pub fn restore(early: bool, value: &mut i32) -> i32 {
    let saved = *value;
    let guard = Guard { slot: value, saved };
    let moved = guard;
    *moved.slot = 7;
    if early {
        return *moved.slot;
    }
    *moved.slot = 9;
    *moved.slot
}
