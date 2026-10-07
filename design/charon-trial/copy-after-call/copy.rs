fn replace_first(words: &mut [u32; 4]) {
    words[0] = 5;
}

pub fn copy_after_call() -> u32 {
    let mut words = [1, 2, 3, 4];
    replace_first(&mut words);
    let copied = words;
    words[0] = 9;
    copied[0]
}
