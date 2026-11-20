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
    step_until(loop(0).entry);
    have prefix(bytes, i) == 0 by {
        unfold(prefix(bytes, i)); solve();
    }
    loop {
        decreases bytes.len() - i;
        invariant i <= bytes.len();
        invariant 0 <= total and total <= 255 * i;
        invariant total == prefix(bytes, i);
        maintain by {
            step_until(read(0).entry); step();
            have i < 18446744073709551615u64;
            have prefix(bytes, i + 1u64) == prefix(bytes, i) + to_integer(bytes[i] as i32) by {
                unfold(prefix(bytes, i + 1u64));
                solve();
            }
            step_until(assignment(i, 1).entry);
            have 0 <= total;
            have to_integer(total) <= 255 * to_integer(i + 1u64);
            have total == prefix(bytes, i + 1u64);
            step();
        }
    }
    have i == bytes.len();
    have prefix(bytes, i) == prefix(bytes, bytes.len()) by {
        rewrite(i, bytes.len());
        solve();
    }
}
