import click::integer;

verifying "enumerate.rs";

// `for (i, x) in xs.iter().enumerate()` is read through `iter.len()`, the
// elements left: each iteration yields index `xs.len() - iter.len()` and the
// element there, then advances.

fn last_index(bytes: &[u8]) -> usize {
    views bytes[0..bytes.len()];
    ensures bytes.len() != 0u64 implies result == bytes.len() - 1u64;
} by {
    step_until(loop(0));
    loop {
        decreases iter.len();
        views bytes[0..bytes.len()];
        invariant iter.len() <= bytes.len();
        invariant iter.len() != bytes.len() implies last == bytes.len() - iter.len() - 1u64;
        preserve by {
            mark iteration;
            step_until(back_edge());
            have 1 <= to_integer(at(iteration, iter.len()));
            have to_integer(at(iteration, iter.len())) <= to_integer(bytes.len());
            apply(integer::uint64_subtract_to_integer(at(iteration, iter.len()), 1u64)) using {
                1 <= to_integer(at(iteration, iter.len()));
            };
            apply(integer::uint64_subtract_to_integer(bytes.len(), at(iteration, iter.len()))) using {
                to_integer(at(iteration, iter.len())) <= to_integer(bytes.len());
            };
            have to_integer(iter.len()) == to_integer(at(iteration, iter.len())) - 1 by { known(); }
            have to_integer(last) == to_integer(bytes.len()) - to_integer(at(iteration, iter.len())) by { known(); }
        }
    }
    have loop(0).iter.len() == 0u64;
    have bytes.len() != 0u64 implies last == bytes.len() - 1u64 by {
        intro();
        have loop(0).iter.len() != bytes.len();
        have to_integer(last) == to_integer(bytes.len()) - to_integer(loop(0).iter.len()) - 1;
        solve();
    }
}

// A reference pattern binds the element's address, read by `*word`.
fn last_pair(words: &[u16]) -> u32 {
    views words[0..words.len()];
    ensures result <= 65535u32;
} by {
    step_until(loop(0));
    loop {
        decreases iter.len();
        views words[0..words.len()];
        invariant iter.len() <= words.len();
        invariant iter.len() != words.len() implies index == words.len() - iter.len() - 1u64;
        invariant value <= 65535u32;
        preserve by {
            mark iteration;
            step_until(back_edge());
            have 1 <= to_integer(at(iteration, iter.len()));
            have to_integer(at(iteration, iter.len())) <= to_integer(words.len());
            apply(integer::uint64_subtract_to_integer(at(iteration, iter.len()), 1u64)) using {
                1 <= to_integer(at(iteration, iter.len()));
            };
            apply(integer::uint64_subtract_to_integer(words.len(), at(iteration, iter.len()))) using {
                to_integer(at(iteration, iter.len())) <= to_integer(words.len());
            };
            have to_integer(iter.len()) == to_integer(at(iteration, iter.len())) - 1 by { known(); }
            have to_integer(index) == to_integer(words.len()) - to_integer(at(iteration, iter.len())) by { known(); }
        }
    }
}
