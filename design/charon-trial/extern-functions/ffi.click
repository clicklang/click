verifying "ffi.rs";

extern fn extern_functions::clamp_reading(raw: i32) -> i32 {
    requires raw >= 0;
    ensures 0 <= result and result <= 100;
}

fn extern_functions::caller(raw: i32) -> i32 {
    requires raw >= 0;
    ensures 1 <= result and result <= 101;
} by { execute(); simp(); }
