verifying "e.rs";
fn value(amount: Amount) -> i32 {
    requires match amount { Amount::Credit(x) => 0i32, Amount::Debit(x) => x } >= -1000000i32;
    requires match amount { Amount::Credit(x) => 0i32, Amount::Debit(x) => x } <= 1000000i32;
    ensures result == match amount {
        Amount::Credit(x) => x as i32,
        Amount::Debit(x) => 0i32 - x,
    };
}
