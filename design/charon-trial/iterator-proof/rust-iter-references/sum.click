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
    execute_until(loop(0));
    have prefix(bytes, bytes.len() - iter_remaining) == 0 by {
        have to_integer(bytes.len() - iter_remaining) <= to_integer(0u64) by auto();
        peel(prefix(bytes, bytes.len() - iter_remaining)) using {
            to_integer(bytes.len() - iter_remaining) <= to_integer(0u64);
        }; simp();
    }
    loop {
        decreases iter_remaining;
        views bytes[0..bytes.len()];
        invariant bytes.len() <= 1000u64;
        invariant iter_remaining <= bytes.len();
        invariant iter_cursor == bytes + (bytes.len() - iter_remaining);
        invariant 0 <= to_integer(total) and to_integer(total) <= 255 * to_integer(bytes.len() - iter_remaining);
        invariant to_integer(total) == prefix(bytes, bytes.len() - iter_remaining);
        preserve by {
            mark iteration;
            have bytes.len() - iter_remaining < bytes.len() by auto();
            have to_integer((bytes.len() - iter_remaining)) <= 1000 by auto();
            have (bytes.len() - iter_remaining) < 1000u64 by auto();
            have (bytes.len() - iter_remaining) < 18446744073709551615u64 by auto();
            have prefix(bytes, (bytes.len() - iter_remaining) + 1u64) == prefix(bytes, (bytes.len() - iter_remaining)) + to_integer(bytes[(bytes.len() - iter_remaining)] as i32) by {
                have to_integer(0u64) <= to_integer(bytes.len() - iter_remaining) by auto();
                have to_integer(bytes.len() - iter_remaining) < to_integer(18446744073709551615u64) by auto();
                peel(prefix(bytes, (bytes.len() - iter_remaining) + 1u64)) using {
                    to_integer(0u64) <= to_integer(bytes.len() - iter_remaining);
                    to_integer(bytes.len() - iter_remaining) < to_integer(18446744073709551615u64);
                };
                simp();
            }
            have to_integer((bytes.len() - iter_remaining)) + 1 <= 18446744073709551615 by auto();
            have to_integer((bytes.len() - iter_remaining) + 1u64) == to_integer((bytes.len() - iter_remaining)) + 1 by auto();
            execute_until(read(0));
            let { result: loaded_byte } = step();
            mark loaded;
            have at(iteration, bytes[(bytes.len() - iter_remaining)]) == loaded_byte;
            have 0 <= to_integer(loaded_byte as i32) by auto();
            have to_integer(loaded_byte as i32) <= 255 by auto();
            have defined(total + loaded_byte as i32) by auto();
            have to_integer(total + loaded_byte as i32) == to_integer(total) + to_integer(loaded_byte as i32) by auto();
            have 0 <= to_integer(total + loaded_byte as i32) by auto();
            have to_integer(total + loaded_byte as i32) <= 255 * at(iteration, to_integer((bytes.len() - iter_remaining) + 1u64)) by auto();
            have (bytes.len() - iter_remaining) == (bytes.len() - at(iteration, iter_remaining)) + 1u64 by auto();
            have to_integer(bytes.len() - iter_remaining) == to_integer((bytes.len() - at(iteration, iter_remaining)) + 1u64) by auto();
            mark addition;
            execute_until(assignment(total, 1)); step();
            execute_until(back_edge());
            have iter_remaining <= bytes.len() by auto();
            have at(iteration, iter_cursor) == bytes + at(iteration, (bytes.len() - iter_remaining)) by auto();
            have to_integer(at(iteration, (bytes.len() - iter_remaining))) < to_integer(18446744073709551615u64) by auto();
            have at(iteration, iter_cursor) + 1 == bytes + ((bytes.len() - at(iteration, iter_remaining)) + 1u64) by {
                arithmetic() using {
                    at(iteration, iter_cursor) == bytes + at(iteration, (bytes.len() - iter_remaining));
                    to_integer(at(iteration, (bytes.len() - iter_remaining))) < to_integer(18446744073709551615u64);
                };
            }
            have iter_remaining < at(iteration, iter_remaining) by auto();
        }
    }
    have iter_remaining == 0u64 by auto();
    have (bytes.len() - iter_remaining) == bytes.len() by auto();
    execute();
    auto();
}
