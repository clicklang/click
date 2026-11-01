verifying "r.rs";
fn countdown(n: i32) -> i32 { decreases n; ensures result == 0i32; }
fn countdown64(n: i64) -> i64 { decreases n; ensures result == 0i64; }
