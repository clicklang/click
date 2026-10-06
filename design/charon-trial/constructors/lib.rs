pub struct Value { pub a: u32, pub b: u32 }
impl Default for Value { fn default() -> Self { Self { a: 1, b: 0 } } }
impl Value { pub fn new() -> Self { Self::default() } }
pub fn entry() -> u32 { let v = Value::new(); v.a }
