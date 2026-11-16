import click::integer;
verifying "quad.rs";
fn quad::load(bytes: &[u8]) -> quad::Quad {
 requires bytes.len() == 4u64; views bytes[0..4];
 ensures result.lanes[0] == bytes[0];
 ensures result.lanes[1] == bytes[1];
 ensures result.lanes[2] == bytes[2];
 ensures result.lanes[3] == bytes[3];
}
fn quad::walk(bytes: &[u8]) -> u32 {
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
        preserve by {
            if 4u64 <= iter.v.len() {
                have to_integer(16u64 - iter.v.len()) + 4 <= 16;
                have to_integer((16u64 - iter.v.len()) + 4u64) <= 16;
                have to_integer(16u64 - iter.v.len()) < 16;
                have to_integer(16u64 - iter.v.len()) + 4 <= 18446744073709551615;
                have (bytes + (16u64 - iter.v.len())) + 4u64 == bytes + ((16u64 - iter.v.len()) + 4u64);
                mark taken;
                step_until(assignment(chunk, 0)); step(); step();
                have chunk == bytes + (16u64 - at(taken, iter.v.len()));
                have chunk_len == 4u64;
                mark before;
                step_until(assignment(_byte, 0));
                have lanes.lanes[0] == at(before, chunk[0]);
                have lanes.lanes[0] == chunk[0];
                have lanes.lanes[1] == at(before, chunk[1]);
                have lanes.lanes[1] == chunk[1];
                have lanes.lanes[2] == at(before, chunk[2]);
                have lanes.lanes[2] == chunk[2];
                have lanes.lanes[3] == at(before, chunk[3]);
                have lanes.lanes[3] == chunk[3];

                have array[0] == chunk[0];
                have array[1] == chunk[1];
                have array[2] == chunk[2];
                have array[3] == chunk[3];
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
