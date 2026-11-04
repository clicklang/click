import click::integer;

verifying "sum.rs";
function prefix(bytes: &[u8], end: usize) -> Integer {
    (0..end).fold(0, |acc, k| {
        acc + to_integer(bytes[k] as i32)
    })
}
fn sum(bytes: &[u8]) -> i32 {
    requires bytes.len() <= 1000u64;
    views bytes[0..bytes.len()];
    ensures to_integer(result) == old(prefix(bytes, bytes.len()));
} by {
    step_until(loop(0));
    have prefix(bytes, bytes.len() - loop(0).iter.len()) == 0 by {
        have to_integer(bytes.len() - loop(0).iter.len()) <= to_integer(0u64);
        peel(prefix(bytes, bytes.len() - loop(0).iter.len())) using {
            to_integer(bytes.len() - loop(0).iter.len()) <= to_integer(0u64);
        }; solve();
    }
    loop {
        decreases iter.len();
        views bytes[0..bytes.len()];
        invariant bytes.len() <= 1000u64;
        invariant iter.len() <= bytes.len();
        invariant 0 <= to_integer(total) and to_integer(total) <= 255 * to_integer(bytes.len() - iter.len());
        invariant to_integer(total) == prefix(bytes, bytes.len() - iter.len());
        preserve by {
            mark iteration;
            have bytes.len() - iter.len() < bytes.len();
            have to_integer((bytes.len() - iter.len())) <= 1000;
            have (bytes.len() - iter.len()) < 1000u64;
            have (bytes.len() - iter.len()) < 18446744073709551615u64;
            have prefix(bytes, (bytes.len() - iter.len()) + 1u64) == prefix(bytes, (bytes.len() - iter.len())) + to_integer(bytes[(bytes.len() - iter.len())] as i32) by {
                have to_integer(0u64) <= to_integer(bytes.len() - iter.len());
                have to_integer(bytes.len() - iter.len()) < to_integer(18446744073709551615u64);
                peel(prefix(bytes, (bytes.len() - iter.len()) + 1u64)) using {
                    to_integer(0u64) <= to_integer(bytes.len() - iter.len());
                    to_integer(bytes.len() - iter.len()) < to_integer(18446744073709551615u64);
                };
                solve();
            }
            have to_integer((bytes.len() - iter.len())) + 1 <= 18446744073709551615;
            have to_integer((bytes.len() - iter.len()) + 1u64) == to_integer((bytes.len() - iter.len())) + 1;
            step_until(read(0));
            let { result: loaded_byte } = step();
            mark loaded;
            have at(iteration, bytes[(bytes.len() - iter.len())]) == loaded_byte;
            have 0 <= to_integer(loaded_byte as i32);
            have to_integer(loaded_byte as i32) <= 255;
            have defined(total + loaded_byte as i32);
            have to_integer(total + loaded_byte as i32) == to_integer(total) + to_integer(loaded_byte as i32);
            have 0 <= to_integer(total + loaded_byte as i32);
            have to_integer(total + loaded_byte as i32) <= 255 * at(iteration, to_integer((bytes.len() - iter.len()) + 1u64));
            have (bytes.len() - iter.len()) == (bytes.len() - at(iteration, iter.len())) + 1u64;
            have to_integer(bytes.len() - iter.len()) == to_integer((bytes.len() - at(iteration, iter.len())) + 1u64);
            mark addition;
            step_until(assignment(total, 1)); step();
            step_until(back_edge());
            have iter.len() <= bytes.len();
            have to_integer(at(iteration, (bytes.len() - iter.len()))) < to_integer(18446744073709551615u64);
            have iter.len() < at(iteration, iter.len());
        }
    }
    have loop(0).iter.len() == 0u64;
    have (bytes.len() - loop(0).iter.len()) == bytes.len();
}
