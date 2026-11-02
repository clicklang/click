verifying "errors.rs";

// A crate enum is the error type of a `Result`: `Result<u32, ParseError>`
// holds a `ParseError` value, constructed and matched as the sidecar's own
// `spec enum ParseError`.
fn check(x: u32) -> Result<u32, ParseError> {
    ensures x == 0u32 implies result == Result<u32, ParseError>::Err(ParseError::Empty);
    ensures x > 100u32 implies result == Result<u32, ParseError>::Err(ParseError::TooBig(x));
    ensures x != 0u32 implies x <= 100u32 implies result == Result<u32, ParseError>::Ok(x);
}

// `?` passes the `ParseError` on unchanged, whichever variant it is.
fn forwarded(x: u32) -> Result<u32, ParseError> {
    ensures x == 0u32 implies result == Result<u32, ParseError>::Err(ParseError::Empty);
    ensures x > 100u32 implies result == Result<u32, ParseError>::Err(ParseError::TooBig(x));
    ensures x != 0u32 implies x <= 100u32 implies result == Result<u32, ParseError>::Ok(x);
}

// Where `check` succeeds, `?` reads its payload.
fn doubled(x: u32) -> Result<u32, ParseError> {
    requires x != 0u32;
    requires x <= 100u32;
    ensures result == Result<u32, ParseError>::Ok(x * 2u32);
}

// A `match` reads the error's own variant and field.
fn describe(x: u32) -> u32 {
    ensures x == 0u32 implies result == 0u32;
    ensures x > 100u32 implies result == x;
    ensures x != 0u32 implies x <= 100u32 implies result == x;
}

// An `Option` may hold a crate enum too.
fn wrapped(e: ParseError) -> Option<ParseError> {
    ensures result == Option<ParseError>::Some(e);
}

fn unwrapped(x: u32) -> u32 {
    ensures result == x;
}
