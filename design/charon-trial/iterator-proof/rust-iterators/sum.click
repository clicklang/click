import click::integer;
import click::rust::slice;
import click::rust::slice_iter;

verifying "sum.rs";
function prefix(bytes: &[u8], end: usize) -> Integer {
    (0..end).fold(0, |acc, k| {
        acc + to_integer(bytes[k] as i32)
    })
}
theorem pointer_association(base: const uint8*, p: uint64, q: uint64) {
    requires to_integer(p) + to_integer(q) <= 18446744073709551615;
    ensures (base + p) + q == base + (p + q) by {
        apply(integer::uint64_add_to_integer(p, q));
        solve() using { to_integer(p + q) == to_integer(p) + to_integer(q); };
    }
}
fn sum(bytes: &[u8]) -> i32 {
    requires bytes.len() <= 1000u64;
    views bytes[0..bytes.len()];
    ensures result == old(prefix(bytes, bytes.len()));
} by {
    step_until(loop(0));
    have loop(0).iter.len() == bytes.len();
    have loop(0).iter.as_slice().as_ptr() == bytes;
    have bytes.len() - loop(0).iter.len() == 0u64;
    have prefix(bytes, bytes.len() - loop(0).iter.len()) == 0 by {
        rewrite(bytes.len() - loop(0).iter.len() == 0u64);
        have 0u64 <= 0u64;
        peel(prefix(bytes, 0u64)) using { 0u64 <= 0u64; };
        solve();
    }
    have 0 <= total and total <= 255 * (bytes.len() - loop(0).iter.len());
    have total == prefix(bytes, bytes.len() - loop(0).iter.len());
    loop {
        decreases iter.len();
        views bytes[0..bytes.len()];
        invariant bytes.len() <= 1000u64;
        invariant iter.len() <= bytes.len();
        invariant iter.as_slice().as_ptr() == bytes + (bytes.len() - iter.len());
        invariant 0 <= total and total <= 255 * (bytes.len() - iter.len());
        invariant total == prefix(bytes, bytes.len() - iter.len());
        preserve by {
            if 0u64 < iter.len() {
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
                have to_integer(bytes.len() - iter.len()) + 1 <= 18446744073709551615;
                step_until(read(0));
                have iter.len() == at(iteration, iter.len()) - 1u64;
                have iter.as_slice().as_ptr() == (bytes + (bytes.len() - at(iteration, iter.len()))) + 1u64;
                apply(pointer_association(bytes, bytes.len() - at(iteration, iter.len()), 1u64));
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
                have iter.as_slice().as_ptr() == bytes + (bytes.len() - iter.len()) by {
                    rewrite((bytes.len() - iter.len()) == (bytes.len() - at(iteration, iter.len())) + 1u64);
                    assumption();
                }
                have iter.len() < at(iteration, iter.len());
                have 0 <= total;
                have to_integer(total) <= 255 * (bytes.len() - iter.len());
            } else {
                have iter.len() == 0u64;
                step(); step(); step(); step(); step();
            }
        }
    }
    have loop(0).iter.len() == 0u64;
    have prefix(bytes, bytes.len() - loop(0).iter.len()) == prefix(bytes, bytes.len()) by {
        rewrite(loop(0).iter.len() == 0u64);
        solve();
    }
}
