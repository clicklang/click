pub fn has_zero(xs: &[u8]) -> bool {
    let mut i = 0;
    while i < xs.len() {
        if xs[i] == 0 {
            return true;
        }
        i += 1;
    }
    false
}

pub fn position(xs: &[u8], v: u8) -> usize {
    for i in 0..xs.len() {
        if xs[i] == v {
            return i;
        }
    }
    xs.len()
}

pub fn find_pair(n: u32, m: u32) -> u32 {
    let mut i = 0;
    while i < n {
        let mut j = 0;
        while j < m {
            if i + j == 7 {
                return i;
            }
            j += 1;
        }
        i += 1;
    }
    n
}

pub fn first_hit(n: u32, m: u32) -> u32 {
    let mut found = 0;
    let mut i = 0;
    'outer: while i < n {
        let mut j = 0;
        while j < m {
            if j == 3 {
                found = i;
                break 'outer;
            }
            j += 1;
        }
        i += 1;
    }
    found
}

pub fn first_row(n: u32, m: u32) -> u32 {
    let mut row = n;
    'outer: for i in 0..n {
        for j in 0..m {
            if j == 4 {
                row = i;
                break 'outer;
            }
        }
    }
    row
}

pub fn skip_rows(n: u32, m: u32) -> u32 {
    let mut count = 0;
    let mut i = 0;
    'rows: while i < n {
        i += 1;
        let mut j = 0;
        while j < m {
            j += 1;
            if j == 2 {
                continue 'rows;
            }
            count = j;
        }
    }
    count
}
