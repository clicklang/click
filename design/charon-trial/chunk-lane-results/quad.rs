pub struct Quad { pub lanes: [u32; 4] }
pub fn load(bytes: &[u8]) -> Quad {
    Quad { lanes: [bytes[0] as u32, bytes[1] as u32, bytes[2] as u32, bytes[3] as u32] }
}
pub fn walk(bytes: &[u8]) -> u32 {
    let iter = bytes.chunks_exact(4);
    for chunk in iter {
        let lanes = load(chunk);
        let _byte = lanes.lanes[1];
    }
    0
}
