import click::integer;
import click::rust::slice;

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
        close() using { to_integer(p + q) == to_integer(p) + to_integer(q); };
    }
}
fn sum(bytes: &[u8]) -> i32 {
    requires bytes.len() <= 1000u64;
    views bytes[0..bytes.len()];
    ensures to_integer(result) == old(prefix(bytes, bytes.len()));
} by {
    step_until(loop(0).entry);
    have loop(0).iter.len() == bytes.len();
    have loop(0).iter.as_slice() == bytes;
    have bytes.len() - loop(0).iter.len() == 0u64;
    have prefix(bytes, bytes.len() - loop(0).iter.len()) == 0 by {
        rewrite(bytes.len() - loop(0).iter.len(), 0u64);
        have 0u64 <= 0u64;
        unfold(prefix(bytes, 0u64));
        solve();
    }
    have 0 <= to_integer(total) and to_integer(total) <= 255 * to_integer(bytes.len() - loop(0).iter.len());
    have to_integer(total) == prefix(bytes, bytes.len() - loop(0).iter.len());
    loop {
        decreases iter.len();
        views bytes[0..bytes.len()];
        invariant bytes.len() <= 1000u64;
        invariant iter.len() <= bytes.len();
        invariant iter.as_slice() == bytes + (bytes.len() - iter.len());
        invariant 0 <= to_integer(total) and to_integer(total) <= 255 * to_integer(bytes.len() - iter.len());
        invariant to_integer(total) == prefix(bytes, bytes.len() - iter.len());
        maintain by {
            step(); step();
            if 0u64 < iter.len() {
                mark iteration;
                have bytes.len() - iter.len() < bytes.len();
                have to_integer((bytes.len() - iter.len())) <= 1000;
                have (bytes.len() - iter.len()) < 1000u64;
                have (bytes.len() - iter.len()) < 18446744073709551615u64;
                have prefix(bytes, (bytes.len() - iter.len()) + 1u64) == prefix(bytes, (bytes.len() - iter.len())) + to_integer(bytes[(bytes.len() - iter.len())] as i32) by {
                    have to_integer(0u64) <= to_integer(bytes.len() - iter.len());
                    have to_integer(bytes.len() - iter.len()) < to_integer(18446744073709551615u64);
                    unfold(prefix(bytes, (bytes.len() - iter.len()) + 1u64));
                    solve();
                }
                have to_integer((bytes.len() - iter.len())) + 1 <= 18446744073709551615;
                have to_integer((bytes.len() - iter.len()) + 1u64) == to_integer((bytes.len() - iter.len())) + 1;
                // `next` binds `byte` to the element, then moves the slice on.
                step_until(assignment(byte, 0).entry);
                step();
                have byte == bytes + (bytes.len() - at(iteration, iter.len()));
                step(); step();
                have iter.len() == at(iteration, iter.len()) - 1u64;
                have iter.as_slice() == (bytes + (bytes.len() - at(iteration, iter.len()))) + 1u64;
                apply(pointer_association(bytes, bytes.len() - at(iteration, iter.len()), 1u64));
                have iter.as_slice() == bytes + ((bytes.len() - at(iteration, iter.len())) + 1u64) by {
                    rewrite(bytes + ((bytes.len() - at(iteration, iter.len())) + 1u64), (bytes + (bytes.len() - at(iteration, iter.len()))) + 1u64);
                    known();
                }
                step_until(read(0).entry);
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
                step_until(assignment(total, 1).entry); step();
                step_until(loop.back_edge);
                have iter.len() <= bytes.len();
                have iter.as_slice() == bytes + (bytes.len() - iter.len()) by {
                    rewrite((bytes.len() - iter.len()), (bytes.len() - at(iteration, iter.len())) + 1u64);
                    known();
                }
                have iter.len() < at(iteration, iter.len());
            } else {
                have iter.len() == 0u64;
                step(); step(); step();
            }
        }
    }
    have loop(0).iter.len() == 0u64;
    have (bytes.len() - loop(0).iter.len()) == bytes.len();
}
