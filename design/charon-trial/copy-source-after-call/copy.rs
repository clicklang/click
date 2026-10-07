#[derive(Clone, Copy)]
pub struct Words([u32; 4]);
fn set(words: &mut Words, value: u32) { words.0[0] = value; }
fn consume(target: &mut Words, other: Words) { target.0[0] = other.0[0]; }
pub fn caller(value: u32) -> u32 {
    let mut words = Words([0; 4]);
    let mut target = Words([0; 4]);
    set(&mut words, value);
    consume(&mut target, words);
    words.0[0]
}
