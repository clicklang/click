verifying "boxed.rs";

fn boxed::boxed(x: u32) -> u32 {
    requires x < 100;
    ensures result == x + 1;
} by { execute(); simp(); }
