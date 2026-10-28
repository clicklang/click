verifying "bools.rs";

fn light_flag(l: Light) -> bool {
    ensures result == (match l { Light::On(b) => b, Light::Off => false });
}

fn make_light(b: bool) -> Light {
    ensures result == Light::On(b);
}

fn option_flag(o: Option<bool>) -> bool {
    ensures o == Option<bool>::Some(true) implies result == false;
    ensures o == Option<bool>::Some(false) implies result;
    ensures o == Option<bool>::None implies result;
}

fn less(a: i32, b: i32) -> bool {
    ensures result == (a < b);
}

fn in_range(x: i32) -> bool {
    ensures result == (0 <= x and x < 10);
}

fn differs(a: bool, b: bool) -> bool {
    ensures result == (a != b);
}

fn neither(a: bool, b: bool) -> bool {
    ensures result implies not a and not b;
    ensures not a and not b implies result;
}

fn all_below(a: i32, b: i32, c: i32, limit: i32) -> bool {
    ensures result == (a < limit and b < limit and c < limit);
}
