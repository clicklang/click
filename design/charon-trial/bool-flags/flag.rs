// A loop guarded by a `bool` local: a claim on the local and the
// program's own test of it are one fact, so an invariant guarded by the
// flag holds on the pass the guard decides.

pub fn scan(n: u32) -> u32 {
    let mut found = false;
    let mut t = 0u32;
    while !found && t < n {
        if t == 7 {
            found = true;
        }
        t += 1;
    }
    t
}
