pub enum ParseError {
    Empty,
    TooBig(u32),
}

pub fn check(x: u32) -> Result<u32, ParseError> {
    if x == 0 {
        Err(ParseError::Empty)
    } else if x > 100 {
        Err(ParseError::TooBig(x))
    } else {
        Ok(x)
    }
}

pub fn forwarded(x: u32) -> Result<u32, ParseError> {
    let v = check(x)?;
    Ok(v)
}

pub fn doubled(x: u32) -> Result<u32, ParseError> {
    let v = check(x)?;
    Ok(v * 2)
}

pub fn describe(x: u32) -> u32 {
    match check(x) {
        Ok(v) => v,
        Err(ParseError::Empty) => 0,
        Err(ParseError::TooBig(n)) => n,
    }
}

pub fn wrapped(e: ParseError) -> Option<ParseError> {
    Some(e)
}

pub fn unwrapped(x: u32) -> u32 {
    match wrapped(ParseError::TooBig(x)) {
        Some(ParseError::TooBig(n)) => n,
        _ => 0,
    }
}
