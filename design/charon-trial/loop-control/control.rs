pub fn scan(n: i32) -> i32 {
    let mut i = n;
    while i > 0 {
        if i == 3 {
            break;
        }
        i -= 1;
    }
    i
}

pub fn first_stop(n: i32, limit: i32) -> i32 {
    let mut i = 0;
    let stop = loop {
        if i >= limit || i >= n {
            break i;
        }
        i += 1;
    };
    stop
}

pub fn count_evens(n: i32) -> i32 {
    let mut i = 0;
    let mut evens = 0;
    while i < n {
        i += 1;
        if i % 2 == 1 {
            continue;
        }
        evens += 1;
    }
    evens
}

pub fn countdown(n: i16) -> i16 {
    let mut i = n;
    while i > 0 {
        i -= 1;
    }
    i
}

pub fn count_to(n: u32) -> u32 {
    let mut i = 0u32;
    while i < n {
        i += 1;
    }
    i
}

pub fn countdown_wide(n: i64) -> i64 {
    let mut i = n;
    while i > 0 {
        i -= 1;
    }
    i
}

pub fn countdown_unsigned(n: u64) -> u64 {
    let mut i = n;
    while i > 0 {
        i -= 1;
    }
    i
}
