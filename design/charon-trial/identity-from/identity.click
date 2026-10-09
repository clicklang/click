verifying "identity.rs";
fn identity(x: u16) -> u16 { ensures result == x; } by { execute(); simp(); }
