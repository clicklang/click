verifying "inclusive.rs";

// A nonempty range starts at the next value to count.
fn count_through(n: u32) -> u32 {
    requires n < 4294967295u32;
    ensures result == n + 1;
} by {
    step_until(loop(0));
    loop {
        decreases n + 1 - total;
        invariant total <= n + 1;
        invariant iter.is_empty() == false implies iter.end() == n;
        invariant to_integer(total) == (if iter.is_empty() { to_integer(n) + 1 } else { to_integer(iter.start()) });
        preserve by {
            mark iteration;
            have iter.is_empty() == false;
            have iter.end() == n;
            have total == iter.start();
            have iter.start() <= n;
            have total <= 4294967294u32;
            if at(iteration, iter.start()) < n {
                step_until(back_edge());
                have to_integer(total) == to_integer(at(iteration, total)) + 1;
                have to_integer(iter.start()) == to_integer(at(iteration, iter.start())) + 1;
                have total == iter.start();
                have iter.start() <= n;
                have iter.is_empty() == false;
                have total <= n + 1;
                have iter.end() == n;
                have iter.is_empty() == false implies iter.end() == n by {
                    intro();
                    known();
                }
            } else {
                have iter.start() == n;
                step_until(back_edge());
                have iter.is_empty();
                have to_integer(total) == to_integer(at(iteration, total)) + 1;
                have total == n + 1;
                have total <= n + 1;
                have not (iter.is_empty() == false);
                have iter.is_empty() == false implies iter.end() == n by {
                    intro();
                    contradiction(iter.is_empty() == false);
                }
            }
        }
    }
    have loop(0).iter.is_empty();
    have total == n + 1;
    step_until(function.exit);
    solve();
}

// The last byte is counted even though its successor cannot fit in a byte.
fn every_byte() -> u32 {
    ensures result == 256u32;
} by {
    step_until(loop(0));
    loop {
        decreases 256u32 - total;
        invariant total <= 256u32;
        invariant iter.is_empty() == false implies iter.end() == 255u8;
        invariant iter.is_empty() == false implies total == (iter.start() as u32);
        invariant iter.is_empty() implies total == 256u32;
        preserve by {
            mark iteration;
            have iter.is_empty() == false;
            have total == (iter.start() as u32);
            if at(iteration, iter.start()) < 255u8 {
                step_until(back_edge());
                have iter.is_empty() == false;
                have to_integer(total) == to_integer(at(iteration, total)) + 1;
                have to_integer(iter.start()) == to_integer(at(iteration, iter.start())) + 1;
                have to_integer(total) == to_integer(iter.start());
                have total == (iter.start() as u32);
                have iter.is_empty() implies total == 256u32 by {
                    intro();
                    contradiction(iter.is_empty() == false);
                }
            } else {
                have iter.start() == 255u8;
                step_until(back_edge());
                have iter.is_empty();
                have to_integer(total) == to_integer(at(iteration, total)) + 1;
                have to_integer(at(iteration, total)) == 255;
                have to_integer(total) == 256;
                have total == 256u32;
                have iter.is_empty() implies total == 256u32 by {
                    intro();
                    known();
                }
            }
        }
    }
    have loop(0).iter.is_empty();
    have total == 256u32;
    step_until(function.exit);
    solve();
}
