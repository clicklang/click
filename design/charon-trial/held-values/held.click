verifying "held.rs";

function size(o: Option<u32>) -> u32 {
    match o { Option::Some(v) => v, Option::None => 0u32 }
}

fn held_values::shrink(o: &mut Option<u32>) {
    owns *o;
    requires size(*o) >= 1u32;
    ensures size(*o) + 1 <= size(old(*o));
} by {
    step_until(function.exit);
    unfold(size(*o));
    solve();
}

fn held_values::peek(o: &Option<u32>) -> u32 {
    views *o;
    ensures result == size(*o);
}

fn held_values::make(x: u32) -> Option<u32> {
    ensures size(result) == x;
} by {
    step_until(function.exit);
    unfold(size(result));
    solve();
}

// The arithmetic closing each claim cites `shrink`'s fact about `o`'s new
// value, which a proof writes `o`, read where `shrink` left it.
fn held_values::constructed(x: u32) -> u32 {
    requires x >= 1u32;
    ensures result < x;
} by {
    have size(Option<u32>::Some(x)) == x by { unfold(size(Option<u32>::Some(x))); solve(); }
}

// The value `make` returned, which `o` held before `shrink`, is spelled by
// its call, `<region>.result`.
fn held_values::returned(x: u32) -> u32 {
    requires x >= 1u32;
    ensures result < x;
}
