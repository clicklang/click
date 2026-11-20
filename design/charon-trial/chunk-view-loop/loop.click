import click::integer;
verifying "loop.rs";
fn first(bytes: &[u8]) -> u8 {
    requires bytes.len() == 4u64;
    views bytes[0..4];
    ensures result == bytes[0];
}
fn walk(bytes: &[u8]) -> u32 {
    requires bytes.len() == 16u64;
    views bytes[0..16];
    ensures result == 0u32;
} by {
    step_until(loop(0));
    loop {
        decreases iter.v.len();
        views bytes[0..16];
        invariant bytes.len() == 16u64;
        invariant iter.chunk_size == 4u64;
        invariant iter.v.len() <= 16u64;
        invariant iter.v == bytes + (16u64 - iter.v.len());
        maintain by {
            if 4u64 <= iter.v.len() {
                have to_integer(16u64 - iter.v.len()) + 4 <= 16;
                have to_integer((16u64 - iter.v.len()) + 4u64) <= 16;
                have to_integer(16u64 - iter.v.len()) < 16;
                have to_integer(16u64 - iter.v.len()) + 4 <= 18446744073709551615;
                have (bytes + (16u64 - iter.v.len())) + 4u64 == bytes + ((16u64 - iter.v.len()) + 4u64);
                mark taken;
                step_until(assignment(_byte, 0));
                have chunk == bytes + (16u64 - at(taken, iter.v.len()));
                have chunk.len() == 4u64;
                step_until(loop(0).back_edge());
                have 4u64 <= at(taken, iter.v.len());
                have to_integer(iter.v.len()) == to_integer(at(taken, iter.v.len())) - 4;
                have (16u64 - at(taken, iter.v.len())) + 4u64 == 16u64 - iter.v.len();
                have iter.v == bytes + (16u64 - iter.v.len());
            } else {
                step(); step(); step();
            }
        }
    }
    step_until(function.exit);
    solve();
}
