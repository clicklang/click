pub struct Guard<'a> {
    pub slot: &'a mut i32,
    pub saved: i32,
}
impl Drop for Guard<'_> {
    fn drop(&mut self) {
        *self.slot = self.saved;
    }
}
pub fn guarded_walk(value: &mut i32, n: i32) -> i32 {
    let saved = *value;
    let guard = Guard { slot: value, saved };
    let mut i = 0;
    while i < n {
        let slot = &mut *guard.slot;
        *slot = i;
        i += 1;
    }
    i
}

// The header assigns this local even when its final test is false.
pub fn final_header(n: i32) -> i32 {
    let mut i = 0;
    let mut last;
    while {
        last = i;
        i < n
    } {
        i += 1;
    }
    last
}
