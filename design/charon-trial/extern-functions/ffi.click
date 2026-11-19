import "ffi.interface.click";
verifying "ffi.rs";

fn extern_functions::caller(raw: i32) -> i32 {
    requires raw >= 0;
    ensures 1 <= result and result <= 101;
}
