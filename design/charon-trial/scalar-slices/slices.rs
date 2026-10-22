pub fn first(xs: &[i32]) -> i32 {
    if xs.len() == 0 { 0 } else { xs[0] }
}

pub fn sum(xs: &[u32]) -> u32 {
    let mut total = 0u32;
    let mut i = 0usize;
    while i < xs.len() {
        total = total ^ xs[i];
        i += 1;
    }
    total
}

pub fn zero(xs: &mut [u64]) {
    let mut i = 0usize;
    while i < xs.len() {
        xs[i] = 0;
        i += 1;
    }
}

pub fn set_at(xs: &mut [i64], k: usize, v: i64) {
    xs[k] = v;
}

pub fn get(xs: &[u16], k: usize) -> u16 {
    xs[k]
}

pub fn swap_ends(xs: &mut [i8]) {
    let n = xs.len();
    if n >= 2 {
        let t = xs[0];
        xs[0] = xs[n - 1];
        xs[n - 1] = t;
    }
}

pub fn last(xs: &[i64]) -> i64 {
    let mut v = 0i64;
    for &x in xs {
        v = x;
    }
    v
}

pub fn head(xs: &[u64]) -> u64 {
    if xs.len() > 0 { xs[0] } else { 0 }
}

pub fn head_twice(xs: &[u64]) -> u64 {
    head(xs)
}

pub fn clear_first(xs: &mut [i16]) {
    if xs.len() > 0 {
        xs[0] = 0;
    }
}

pub fn clear_twice(xs: &mut [i16]) {
    clear_first(xs);
    clear_first(xs);
}
