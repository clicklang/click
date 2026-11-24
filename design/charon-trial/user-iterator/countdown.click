verifying "countdown.rs";

impl Iterator for Countdown {
    fn next(&mut self) -> Option<u32> {
        owns *self;
        ensures old(self.n) == 0u32 implies result == Option<u32>::None and self.n == 0u32;
        ensures old(self.n) != 0u32 implies result == Option<u32>::Some(old(self.n) - 1u32) and self.n == old(self.n) - 1u32;
    }
}

fn count(n: u32) -> u32 {
    ensures result == n;
} by {
    step_until(loop(0).entry);
    loop {
        decreases iter.n;
        invariant to_integer(passes) + to_integer(iter.n) == to_integer(n);
        maintain by {
            if 0u32 < iter.n {
                mark iteration;
                have iter.n != 0u32;
                have passes <= 4294967294u32;
                step_until(loop.back_edge);
                have to_integer(iter.n) == to_integer(at(iteration, iter.n)) - 1;
            } else {
                have iter.n == 0u32;
                step(); step(); step();
            }
        }
    }
    step_until(function.exit);
    close();
}

fn last(n: u32) -> u32 {
    ensures result == 0u32;
} by {
    step_until(loop(0).entry);
    loop {
        decreases iter.n;
        invariant (iter.n == n and last == 0u32) or last == iter.n;
        maintain by {
            if 0u32 < iter.n {
                mark iteration;
                have iter.n != 0u32;
                step_until(loop.back_edge);
                have to_integer(iter.n) == to_integer(at(iteration, iter.n)) - 1;
            } else {
                have iter.n == 0u32;
                step(); step(); step();
            }
        }
    }
    have iter.n == 0u32;
    have last == 0u32 by {
        cases {
            iter.n == n and last == 0u32 => { close(); }
            last == iter.n => { close(); }
        }
    }
    step_until(function.exit);
    close();
}
