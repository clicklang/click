pub fn countdown(n: i32) -> i32 {
    if n <= 0 { return 0; }
    countdown(n - 1)
}
pub fn countdown64(n: i64) -> i64 {
    if n <= 0 { return 0; }
    countdown64(n - 1)
}

pub fn unchanged(n: i32) -> i32 {
    if n <= 0 { return 0; }
    unchanged(n)
}
