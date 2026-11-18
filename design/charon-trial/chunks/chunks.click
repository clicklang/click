import click::integer;
verifying "chunks.rs";
fn tail(bytes: &[u8], size: usize) -> usize {
    requires size != 0u64;
    ensures result == bytes.len() % size;
} by {
    step_until(function.exit);
    solve();
}

fn walk(bytes: &[u8]) -> usize {
    views bytes[0..bytes.len()];
    ensures result == bytes.len() % 4u64;
    ensures forall (k: uint64) {
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
    have forall (k: uint64) {
        k < bytes.len() implies bytes[k] == old(bytes[k])
    } by { intro(); intro(); solve(); }
    solve();
}

fn next_len(bytes: &[u8]) -> usize {
    requires bytes.len() == 8u64;
    ensures result == 4u64;
} by {
    step_until(function.exit);
    solve();
}

fn tail_byte(bytes: &[u8]) -> u8 {
    requires bytes.len() == 7u64;
    views bytes[0..7];
    ensures result == old(bytes[4]);
} by {
    have bytes.len() % 4u64 == 3u64;
    have bytes.len() - bytes.len() % 4u64 == 4u64;
    step_until(statement(2));
    have tail.len() == 3u64;
    have tail == bytes + 4u64;
    step_until(function.exit);
    solve();
}
