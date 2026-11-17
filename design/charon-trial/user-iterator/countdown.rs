pub struct Countdown {
    pub n: u32,
}

impl Iterator for Countdown {
    type Item = u32;
    fn next(&mut self) -> Option<u32> {
        if self.n == 0 {
            None
        } else {
            self.n -= 1;
            Some(self.n)
        }
    }
}

pub fn count(n: u32) -> u32 {
    let mut passes = 0u32;
    for _k in (Countdown { n }) {
        passes += 1;
    }
    passes
}

pub fn last(n: u32) -> u32 {
    let mut last = 0u32;
    for k in (Countdown { n }) {
        last = k;
    }
    last
}
