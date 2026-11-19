import click::integer;
verifying "chunks.rs";

fn cover(bytes: &[u8]) -> usize {
    views bytes[0..bytes.len()];
    ensures result == bytes.len() % 4u64;
    ensures forall (k: usize) {
        k < bytes.len() implies bytes[k] == old(bytes[k])
    };
} by {
    step_until(loop(0));
    loop {
        decreases iter.v.len();
        views bytes[0..bytes.len()];
        invariant tail.len() == bytes.len() % 4u64;
        invariant iter.chunk_size == 4u64;
        invariant iter.v.len() <= bytes.len() - bytes.len() % 4u64;
        invariant iter.v == bytes + (bytes.len() - bytes.len() % 4u64 - iter.v.len());
        initialize by {
            have bytes.len() % 4u64 <= bytes.len();
            solve();
        }
        preserve by {
            if 4u64 <= iter.v.len() {
                have bytes.len() % 4u64 <= bytes.len();
                have to_integer(bytes.len() - bytes.len() % 4u64 - iter.v.len()) + 4 <= to_integer(bytes.len());
                have to_integer((bytes.len() - bytes.len() % 4u64 - iter.v.len()) + 4u64) <= to_integer(bytes.len());
                have to_integer(bytes.len() - bytes.len() % 4u64 - iter.v.len()) < to_integer(bytes.len());
                have to_integer(bytes.len() - bytes.len() % 4u64 - iter.v.len()) + 4 <= 18446744073709551615;
                have (bytes + (bytes.len() - bytes.len() % 4u64 - iter.v.len())) + 4u64 == bytes + ((bytes.len() - bytes.len() % 4u64 - iter.v.len()) + 4u64);
                mark head;
                step_until(loop(0).back_edge());
                have (bytes.len() - bytes.len() % 4u64 - at(head, iter.v.len())) + 4u64 == bytes.len() - bytes.len() % 4u64 - iter.v.len();
                have iter.v == bytes + (bytes.len() - bytes.len() % 4u64 - iter.v.len());
            } else {
                step(); step(); step();
            }
        }
    }
    step_until(function.exit);
    have forall (k: usize) {
        k < bytes.len() implies bytes[k] == old(bytes[k])
    } by { intro(); intro(); solve(); }
    solve();
}
