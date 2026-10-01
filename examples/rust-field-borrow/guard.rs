pub struct Guard<'a> {
    pub slot: &'a mut i32,
    pub saved: i32,
}

impl Drop for Guard<'_> {
    fn drop(&mut self) {
        *self.slot = self.saved;
    }
}

pub fn cleanup(value: &mut i32) {
    let mut first = Guard {
        slot: value,
        saved: 1,
    };
    let second = Guard {
        slot: &mut first.saved,
        saved: 42,
    };
}
