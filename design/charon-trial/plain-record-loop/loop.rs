struct Packet { value: i32 }
pub fn packet_walk(n: i32) -> i32 {
    let mut i = 0;
    let mut sum = 0;
    while i < n {
        let packet = Packet { value: 1 };
        sum += packet.value;
        i += 1;
    }
    sum
}
