pub fn take_it(o: &mut Option<u32>) -> Option<u32> {
    let r = *o;
    *o = None;
    r
}

pub fn fill(o: &mut Option<u32>, x: u32) {
    *o = Some(x);
}

pub fn peek(o: &Option<u32>) -> u32 {
    match *o {
        Some(v) => v,
        None => 0,
    }
}

pub fn round(x: u32) -> u32 {
    let mut o = None;
    fill(&mut o, x);
    let r = take_it(&mut o);
    match r {
        Some(v) => v,
        None => 0,
    }
}

pub fn clear(o: &mut Option<u32>) {
    *o = None;
}

pub fn cleared(x: u32) -> u32 {
    let mut o = Some(x);
    clear(&mut o);
    peek(&o)
}

pub fn put<T: Copy>(slot: &mut T, value: T) {
    *slot = value;
}

pub fn replaced<T: Copy>(a: T, b: T) -> T {
    let mut x = a;
    put(&mut x, b);
    x
}

pub fn replaced_u32(a: u32, b: u32) -> u32 {
    replaced(a, b)
}

pub fn bump(x: &mut u32) {
    *x = 7;
}

pub fn bumped() -> u32 {
    let mut a = 1;
    bump(&mut a);
    a
}
