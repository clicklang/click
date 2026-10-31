pub enum Amount {
    Credit(u32),
    Debit(i32),
}

pub fn value(amount: Amount) -> i32 {
    match amount {
        Amount::Credit(x) => x as i32,
        Amount::Debit(x) => -1 * x,
    }
}
