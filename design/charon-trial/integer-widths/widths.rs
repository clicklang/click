pub fn add64(a: u64, b: u64) -> u64 {
    a + b
}

pub fn sub8(x: i8, y: i8) -> i8 {
    x - y
}

pub fn widen16(x: i16) -> i64 {
    x as i64
}

pub fn scale(x: i64) -> i64 {
    x * 3 - 1
}

pub fn diff(a: isize, b: isize) -> isize {
    a - b
}

pub fn narrow(x: u64) -> u8 {
    x as u8
}

pub fn bump(x: &mut i16) {
    *x += 1;
}

pub fn lossless(x: u32) -> u64 {
    u64::from(x)
}

pub fn signed_from(x: i8) -> i64 {
    i64::from(x)
}

pub struct Account {
    pub balance: i64,
    pub id: u64,
}

pub enum Amount {
    Credit(u64),
    Debit(i64),
}

pub fn deposit(account: &mut Account, amount: i64) {
    account.balance += amount;
}

pub fn value(amount: Amount) -> i64 {
    match amount {
        Amount::Credit(x) => x as i64,
        Amount::Debit(x) => x,
    }
}

pub fn classify(x: i8) -> u8 {
    match x {
        0 => 0,
        1 | 2 => 1,
        _ => 2,
    }
}

pub fn first(x: Option<u64>) -> u64 {
    match x {
        Some(v) => v,
        None => 0,
    }
}

pub fn step_below(i: u32, n: u32) -> u32 {
    if i < n { i + 1 } else { i }
}
