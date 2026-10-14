unsafe extern "C" {
    safe fn clamp_reading(raw: i32) -> i32;
}

pub fn caller(raw: i32) -> i32 {
    clamp_reading(raw) + 1
}
