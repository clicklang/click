pub fn single(x: u32) -> Vec<u32> {
    let mut v = Vec::new();
    v.push(x);
    v
}

pub fn count(v: &Vec<u32>) -> usize {
    v.len()
}

pub fn first(v: &Vec<u32>) -> u32 {
    v[0]
}

pub fn append(v: &mut Vec<u32>, x: u32) {
    v.push(x);
}

pub fn pushed_len(x: u32) -> usize {
    let mut v = Vec::new();
    v.push(x);
    v.len()
}

pub fn empty_len() -> usize {
    let v: Vec<u32> = Vec::new();
    v.len()
}

pub fn pair(x: u32, y: u32) -> Vec<u32> {
    let mut v = Vec::with_capacity(2);
    v.push(x);
    v.push(y);
    v
}

pub fn second_of_pair(x: u32, y: u32) -> u32 {
    let v = pair(x, y);
    v[1]
}
