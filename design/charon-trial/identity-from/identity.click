verifying "identity.rs";
uint16 identity(uint16 x) { ensures result == x; } by { execute(); simp(); }
