pub struct Cell {
    value: u32,
}

pub fn taken(x: u32) -> u32 {
    let mut o = Some(Box::new(Cell { value: x }));
    let t = o.take();
    let left = match o {
        Some(_) => 1,
        None => 0,
    };
    match t {
        Some(b) => b.value + left,
        None => 0,
    }
}

pub fn taken_twice(x: u32) -> u32 {
    let mut o = Some(Box::new(Cell { value: x }));
    let first = o.take();
    let second = o.take();
    let a = match first {
        Some(b) => b.value,
        None => 0,
    };
    match second {
        Some(_) => 1,
        None => a,
    }
}

pub fn scalar_taken(x: u32) -> u32 {
    let mut o = Some(x);
    let t = o.take();
    match o {
        Some(_) => 0,
        None => match t {
            Some(v) => v,
            None => 0,
        },
    }
}

pub fn take_param(o: &mut Option<u32>) -> Option<u32> {
    o.take()
}
