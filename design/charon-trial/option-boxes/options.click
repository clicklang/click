verifying "options.rs";

fn option_boxes::maybe(x: u32, make: bool) -> u32 {
    ensures make implies result == x;
    ensures make == false implies result == 0;
}

fn option_boxes::dropped(x: u32, make: bool) -> u32 {
    ensures result == x;
}
