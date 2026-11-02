pub fn ok_if(x: u32, good: bool) -> Result<u32, u8> {
    if good { Ok(x) } else { Err(7) }
}

pub fn or_zero(r: Result<u32, u8>) -> u32 {
    match r {
        Ok(v) => v,
        Err(_) => 0,
    }
}

pub fn round(x: u32) -> u32 {
    or_zero(ok_if(x, true))
}

pub fn plus_one(r: Result<u32, u8>) -> Result<u32, u8> {
    let v = r?;
    Ok(v + 1)
}

pub fn divide(a: u32, b: u32) -> Result<u32, u8> {
    if b == 0 { Err(1) } else { Ok(a / b) }
}

pub fn quarter(x: u32) -> Result<u32, u8> {
    let half = divide(x, 2)?;
    divide(half, 2)
}

pub fn error_code(r: Result<u32, u8>) -> u8 {
    if let Err(code) = r { code } else { 0 }
}

pub fn same<T: Copy, E: Copy>(r: Result<T, E>) -> Result<T, E> {
    let v = r?;
    Ok(v)
}

pub fn kept(x: i32) -> Result<i32, bool> {
    same(Ok(x))
}

pub fn must(r: Result<u32, u8>) -> u32 {
    r.unwrap()
}

pub fn must_say(r: Result<u32, u8>) -> u32 {
    r.expect("a value")
}

pub fn or_default(r: Result<u32, u8>, d: u32) -> u32 {
    r.unwrap_or(d)
}
