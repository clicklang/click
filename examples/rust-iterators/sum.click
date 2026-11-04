verifying "sum.rs";
function prefix(bytes: &[u8], end: usize) -> Integer {
    (0..end).fold(0, |acc, k| {
        acc + to_integer(bytes[k] as i32)
    })
}
fn sum(bytes: &[u8]) -> i32 {
    requires bytes.len() <= 1000u64;
    views bytes[0..bytes.len()];
    ensures result == old(prefix(bytes, bytes.len()));
} by {
    step_until(loop(0));
    have prefix(bytes, bytes.len() - loop(0).iter.len()) == 0 by {
        peel(prefix(bytes, bytes.len() - loop(0).iter.len())) using {
            to_integer(bytes.len() - loop(0).iter.len()) <= 0;
        }; solve();
    }
    loop {
        decreases iter.len();
        views bytes[0..bytes.len()];
        invariant bytes.len() <= 1000u64;
        invariant iter.len() <= bytes.len();
        invariant iter.as_slice() == bytes + (bytes.len() - iter.len());
        invariant 0 <= total and total <= 255 * (bytes.len() - iter.len());
        invariant total == prefix(bytes, bytes.len() - iter.len());
        preserve by {
            mark iteration;
            have 0 <= to_integer(bytes.len() - iter.len());
            have to_integer(bytes.len() - iter.len()) < 18446744073709551615;
            have prefix(bytes, (bytes.len() - iter.len()) + 1u64) == prefix(bytes, (bytes.len() - iter.len())) + to_integer(bytes[(bytes.len() - iter.len())] as i32) by {
                peel(prefix(bytes, (bytes.len() - iter.len()) + 1u64)) using {
                    0 <= to_integer(bytes.len() - iter.len());
                    to_integer(bytes.len() - iter.len()) < 18446744073709551615;
                };
                solve();
            }
            step_until(read(0));
            step();
            have at(iteration, bytes[(bytes.len() - iter.len())]) == byte;
            have defined(total + byte as i32);
            have to_integer(total + byte as i32) == to_integer(total) + to_integer(byte as i32);
            step_until(assignment(total, 1)); step();
            step_until(back_edge());
            have to_integer(iter.len()) == to_integer(at(iteration, iter.len())) - 1;
            have to_integer(bytes.len() - iter.len()) == to_integer(bytes.len()) - to_integer(iter.len());
            have to_integer(bytes.len() - at(iteration, iter.len())) == to_integer(bytes.len()) - to_integer(at(iteration, iter.len()));
            have to_integer((bytes.len() - at(iteration, iter.len())) + 1u64) == to_integer(bytes.len() - at(iteration, iter.len())) + 1;
            have to_integer(bytes.len() - iter.len()) == to_integer((bytes.len() - at(iteration, iter.len())) + 1u64);
            have iter.len() <= bytes.len();
            have iter.len() < at(iteration, iter.len());
            have at(iteration, iter.as_slice()) + 1 == bytes + ((bytes.len() - at(iteration, iter.len())) + 1u64) by {
                solve() using {
                    at(iteration, iter.as_slice()) == bytes + at(iteration, (bytes.len() - iter.len()));
                    at(iteration, to_integer(bytes.len() - iter.len()) < 18446744073709551615);
                };
            }
            have iter.as_slice() == bytes + (bytes.len() - iter.len());
            have 0 <= total;
            have to_integer(total) <= 255 * (bytes.len() - iter.len());
        }
    }
    have loop(0).iter.len() == 0u64;
    have prefix(bytes, bytes.len() - loop(0).iter.len()) == prefix(bytes, bytes.len()) by {
        rewrite(loop(0).iter.len() == 0u64);
        solve();
    }
}
