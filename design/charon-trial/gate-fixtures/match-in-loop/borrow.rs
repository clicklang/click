pub struct C { pub n: u32 }
pub fn take(c: &mut C) -> Option<u32> {
    if c.n == 0 { None } else { c.n -= 1; Some(c.n) }
}
pub fn seen(n: u32) -> u32 {
    let mut c = C { n };
    let mut seen = 0u32;
    let mut last = 0u32;
    let mut k = n;
    while k > 0 {
        k -= 1;
        match take(&mut c) {
            Some(x) => {
                seen += 1;
                last = x;
            }
            None => {}
        }
    }
    seen
}
