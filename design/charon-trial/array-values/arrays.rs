pub fn literal() -> u32 {
    let words = [3u32, 5, 7];
    words[1]
}

pub fn repeated(value: u8) -> u8 {
    let bytes = [value; 4];
    bytes[3]
}

pub fn independent() -> i32 {
    let mut original = [3i32, 5];
    let mut copied = original;
    original[0] = 7;
    copied[1] = 9;
    original[1] + copied[0]
}

pub fn replace() -> u32 {
    let mut words = [3u32, 5];
    words = [words[1], words[0]];
    words[0] + words[1]
}

pub fn copy_reference(words: &[u32; 2]) -> u32 {
    let copied = *words;
    copied[0]
}

pub fn copy_into(target: &mut [u32; 2], source: &[u32; 2]) {
    *target = *source;
}

pub fn zero() -> usize {
    let empty: [u8; 0] = [];
    let copied = empty;
    copied.len()
}

pub fn next(value: &mut u32) -> u32 {
    let before = *value;
    *value = before + 1;
    before
}

pub fn repeat_call(value: &mut u32) -> u32 {
    let words = [next(value); 3];
    words[2]
}

pub fn zero_repeat_call(value: &mut u32) -> usize {
    let words = [next(value); 0];
    words.len()
}

pub fn ordered_calls(value: &mut u32) -> u32 {
    let words = [next(value), next(value)];
    words[1]
}

pub fn borrow_local() -> u32 {
    let mut words = [3u32, 5];
    let child = &mut words;
    child[1] = 7;
    words[0] + words[1]
}

pub fn first_arg(first: u32, _second: u32) -> u32 {
    first
}

pub fn argument_order(value: &mut u32) -> u32 {
    let words = [first_arg(*value, next(value)); 1];
    words[0]
}

pub fn self_copy() -> u8 {
    let mut bytes = [1u8, 2];
    bytes = bytes;
    bytes[1]
}

pub fn assignment_order(value: &mut u32) -> u32 {
    let mut words = [0u32; 6];
    words[next(value) as usize] = *value;
    words[4]
}
