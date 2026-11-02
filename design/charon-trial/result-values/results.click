verifying "results.rs";

fn result_values::ok_if(x: u32, good: bool) -> Result<u32, u8> {
    ensures good implies result == Result<u32, u8>::Ok(x);
    ensures good == false implies result == Result<u32, u8>::Err(7u8);
}

fn result_values::or_zero(r: Result<u32, u8>) -> u32 {
    ensures result == (match r { Result::Ok(v) => v, Result::Err(e) => 0u32 });
}

fn result_values::round(x: u32) -> u32 {
    ensures result == x;
}

// `r?` returns `r`'s `Err` unchanged and otherwise reads `Ok`'s payload.
fn result_values::plus_one(r: Result<u32, u8>) -> Result<u32, u8> {
    requires match r { Result::Ok(v) => v, Result::Err(e) => 0u32 } < 4294967295u32;
    ensures result == (match r { Result::Ok(v) => Result<u32, u8>::Ok(v + 1u32), Result::Err(e) => Result<u32, u8>::Err(e) });
}

fn result_values::divide(a: u32, b: u32) -> Result<u32, u8> {
    ensures b == 0u32 implies result == Result<u32, u8>::Err(1u8);
    ensures b != 0u32 implies result == Result<u32, u8>::Ok(a / b);
}

fn result_values::quarter(x: u32) -> Result<u32, u8> {
    ensures result == Result<u32, u8>::Ok((x / 2u32) / 2u32);
}

fn result_values::error_code(r: Result<u32, u8>) -> u8 {
    ensures result == (match r { Result::Ok(v) => 0u8, Result::Err(e) => e });
}

// Generic functions over `Result<T, E>` are verified once with `T` and `E`
// abstract.
fn result_values::same<T: Copy, E: Copy>(r: Result<T, E>) -> Result<T, E> {
    ensures result == r;
}

fn result_values::kept(x: i32) -> Result<i32, bool> {
    ensures result == Result<i32, bool>::Ok(x);
}

// `unwrap` and `expect` panic on `Err`, so a caller shows the value is `Ok`:
// their contract requires `exists (value: T) { r == Result<T, E>::Ok(value) }`
// and ensures `r == Result<T, E>::Ok(result)`.
fn result_values::must(r: Result<u32, u8>) -> u32 {
    requires exists (v: u32) { r == Result<u32, u8>::Ok(v) };
    ensures r == Result<u32, u8>::Ok(result);
}

// A caller that knows the payload names it as the requirement's witness.
fn result_values::must_say(r: Result<u32, u8>) -> u32 {
    requires r == Result<u32, u8>::Ok(5u32);
    ensures result == 5u32;
} by {
    have exists (value: u32) { r == Result<u32, u8>::Ok(value) } by {
        witness { value: 5u32 };
        solve();
    }
}

fn result_values::or_default(r: Result<u32, u8>, d: u32) -> u32 {
    ensures result == click::result::unwrap_or(r, d);
}
