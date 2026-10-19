verifying "options.rs";

fn option_values::some_if(x: u32, make: bool) -> Option<u32> {
    ensures make implies result == Option<u32>::Some(x);
    ensures make == false implies result == Option<u32>::None;
} by {
    execute();
    simp();
}

fn option_values::or_zero(o: Option<u32>) -> u32 {
    ensures result == (match o { Option::Some(v) => v, Option::None => 0u32 });
} by {
    execute();
    simp();
}

fn option_values::round(x: u32) -> u32 {
    ensures result == x;
} by {
    execute();
    simp();
}
