pub fn first(bytes: &[u8]) -> u8 {
    bytes[0]
}
pub fn set(bytes: &mut [u8]) {
    bytes[1] = 7;
}
pub fn size(bytes: &[u8]) -> usize {
    bytes.len()
}

pub fn array_len(bytes: &[u8; 3]) -> usize {
    size(bytes)
}
pub fn read(bytes: &[u8; 3]) -> u8 {
    let slice: &[u8] = bytes;
    first(slice)
}
pub fn mutate(bytes: &mut [u8; 3]) -> u8 {
    set(bytes);
    bytes[1]
}
pub fn local() -> u8 {
    let mut bytes = [3u8, 5, 9];
    set(&mut bytes);
    first(&bytes) + bytes[1]
}
pub fn alias(bytes: &mut [u8; 3]) -> u8 {
    let slice: &mut [u8] = &mut *bytes;
    set(slice);
    bytes[1]
}
pub fn retarget() -> usize {
    let short = [3u8];
    let long = [5u8; 4];
    let mut slice: &[u8] = &short;
    slice = &long;
    slice.len()
}
pub fn retarget_mut() -> u8 {
    let mut a = [1u8, 2];
    let mut b = [3u8, 4, 5];
    let mut slice: &mut [u8] = &mut a;
    set(slice);
    slice = &mut b;
    set(slice);
    a[1] + b[1]
}
pub fn empty() -> usize {
    let bytes: [u8; 0] = [];
    size(&bytes)
}
pub fn empty_ref(bytes: &[u8; 0]) -> usize {
    let slice: &[u8] = bytes;
    slice.len()
}
pub fn borrow_shared(bytes: &mut [u8; 3]) -> u8 {
    first(bytes)
}
