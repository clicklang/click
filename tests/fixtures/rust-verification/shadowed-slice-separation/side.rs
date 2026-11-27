pub fn add(q: &mut u32, delta: u32) { *q += delta; }

pub fn use_scalar(bytes: &[u8], initial: u32, delta: u32) -> u32 {
    let mut q = initial;
    let (bytes, _) = bytes.split_at(0);
    let _count = bytes.len();
    add(&mut q, delta);
    q
}
