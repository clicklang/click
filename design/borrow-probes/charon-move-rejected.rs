pub struct Token {
    pub value: u16,
}
pub fn rejected(token: Token) -> u16 {
    let moved = token;
    let result = token.value;
    core::mem::drop(moved);
    result
}
