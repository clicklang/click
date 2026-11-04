// A Rust local named like a Click value: `rust(iterations)` names the
// local, and bare `iterations` the loop's pass count.

pub fn count(n: u32) -> u32 {
    let mut iterations = 0;
    while iterations < n {
        iterations += 1;
    }
    iterations
}
