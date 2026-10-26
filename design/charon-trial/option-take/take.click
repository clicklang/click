verifying "take.rs";

// `o.take()` moves the option out and leaves `None`: the box it held is the
// result's, so it is dropped once, with the result.
fn option_take::taken(x: u32) -> u32 {
    ensures result == x;
} by {
    execute();
    solve();
}

// A second `take` finds `None`.
fn option_take::taken_twice(x: u32) -> u32 {
    ensures result == x;
} by {
    execute();
    solve();
}

fn option_take::scalar_taken(x: u32) -> u32 {
    ensures result == x;
} by {
    execute();
    solve();
}

// Through a reference, `o.take()` reads `*o` and stores `None` there.
fn option_take::take_param(o: &mut Option<u32>) -> Option<u32> {
    owns *o;
    ensures result == old(*o);
    ensures *o == Option<u32>::None;
} by {
    execute();
    solve();
}
