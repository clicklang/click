pub struct Guard<'a> {
    pub slot: &'a mut i32,
    pub saved: i32,
}
impl Drop for Guard<'_> {
    fn drop(&mut self) {
        *self.slot = self.saved;
    }
}
pub fn increment(x: u16) -> u16 {
    x + 1
}
pub fn guarded_increment(x: u16, value: &mut i32, early: bool) -> u16 {
    let saved = *value;
    let guard = Guard { slot: value, saved };
    let answer = x + 1;
    *guard.slot = 7;
    if early {
        return answer;
    }
    let moved = guard;
    *moved.slot = 9;
    core::mem::drop(moved);
    answer
}
