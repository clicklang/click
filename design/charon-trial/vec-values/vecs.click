verifying "vecs.rs";

// A `Vec<u32>` is the library's `Vec<uint32>`: a contract reads `v.len()`
// and `v[i]` as the code does, and the library's `vec::push` for the
// vector a push leaves.
fn vec_values::single(x: u32) -> Vec<u32> {
    ensures result.len() == 1u64;
    ensures result[0u64] == x;
}

fn vec_values::count(v: &Vec<u32>) -> usize {
    views *v;
    ensures result == v.len();
}

// `v[0]` panics on an empty vector, so the caller shows it is not.
fn vec_values::first(v: &Vec<u32>) -> u32 {
    views *v;
    requires 0u64 < v.len();
    ensures result == v[0u64];
}

fn vec_values::append(v: &mut Vec<u32>, x: u32) {
    owns *v;
    requires v.len() < 100u64;
    ensures *v == click::rust::vec::push(old(*v), x);
    ensures v.len() == old(v.len()) + 1;
}

fn vec_values::pushed_len(x: u32) -> usize {
    ensures result == 1u64;
}

fn vec_values::empty_len() -> usize {
    ensures result == 0u64;
}

// `Vec::with_capacity` reserves room, which is outside the model: the
// vector is empty.
fn vec_values::pair(x: u32, y: u32) -> Vec<u32> {
    ensures result.len() == 2u64;
    ensures result[1u64] == y;
}

fn vec_values::second_of_pair(x: u32, y: u32) -> u32 {
    ensures result == y;
}
