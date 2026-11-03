// A borrowed `Option` local keeps its value in memory. After a call writes
// through the borrow, the caller knows the new value only through the
// callee's contract, stated about the local's object.

pub fn shrink(o: &mut Option<u32>) {
    *o = None;
}

pub fn peek(o: &Option<u32>) -> u32 {
    match *o {
        Some(v) => v,
        None => 0,
    }
}

pub fn make(x: u32) -> Option<u32> {
    Some(x)
}

pub fn constructed(x: u32) -> u32 {
    let mut o = Some(x);
    shrink(&mut o);
    peek(&o)
}

pub fn returned(x: u32) -> u32 {
    let mut o = make(x);
    shrink(&mut o);
    peek(&o)
}
