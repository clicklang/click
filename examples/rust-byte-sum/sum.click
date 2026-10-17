arithmetic "integer";

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
    execute_until(loop(0));
    have prefix(bytes, i) == 0 by {
        peel(prefix(bytes, i)) using {
            i <= 0u64;
        }; simp();
    }
    loop {
        decreases bytes.len() - i;
        invariant i <= bytes.len();
        invariant 0 <= total and total <= 255 * i;
        invariant total == prefix(bytes, i);
        preserve by {
            execute_until(read(0)); step();
            have defined(bytes[i]) by {
                transport(at(function.entry, viewable(bytes[0..bytes.len()])), defined(bytes[i])) using {
                    at(function.entry, viewable(bytes[0..bytes.len()]));
                    i < bytes.len();
                    bytes.len() <= 9223372036854775807u64;
                };
            }
            have defined(total + bytes[i] as i32) by auto();
            have i < 18446744073709551615u64 by auto();
            have prefix(bytes, i + 1u64) == prefix(bytes, i) + to_integer(bytes[i] as i32) by {
                peel(prefix(bytes, i + 1u64)) using {
                    0u64 <= i;
                    i < 18446744073709551615u64;
                };
                simp();
            }
            execute_until(assignment(i, 1));
            have 0 <= total by auto();
            have to_integer(total) <= 255 * to_integer(i + 1u64) by auto();
            have total == prefix(bytes, i + 1u64) by auto();
            step();
        }
    }
    have i == bytes.len() by auto();
    have prefix(bytes, i) == prefix(bytes, bytes.len()) by {
        rewrite(i == bytes.len());
        simp();
    }
    execute();
}
