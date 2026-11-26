verifying "bytes.rs";

fn length(bytes: &[u8]) -> usize {
    ensures result == bytes.len();
}

fn read(bytes: &[u8], index: usize) -> u8 {
    requires index < bytes.len();
    views *bytes;
    ensures result == bytes[index];
}

fn write(bytes: &mut [u8], index: usize, value: u8) {
    requires index < bytes.len();
    owns *bytes;
    ensures bytes[index] == value;
}

fn first(bytes: &[u8]) -> u8 {
    requires bytes.len() == 4;
    views bytes[0..4];
    ensures result == bytes[0];
}

theorem byte_increment_is_exact(value: uint8) {
    requires to_integer(value) < 255;
    ensures to_integer((value + 1) as uint8) == to_integer(value) + 1 by {
        have 0 <= to_integer(value) + 1;
        apply(click::integer::lt_step_le(to_integer(value), 255));
        close();
    }
}

fn increment_first(bytes: &mut [u8]) {
    requires bytes.len() == 4;
    requires bytes[0] < 255;
    owns bytes[0..4];
    ensures bytes[0] == old(bytes[0]) + 1;
} by {
    step_until(function.exit);
    have old(to_integer(bytes[0])) < 255;
    have bytes[0] == ((old(bytes[0]) + 1) as u8);
    apply(byte_increment_is_exact(old(bytes[0])));
    close();
}

fn empty(bytes: &[u8]) -> bool {
    ensures result == (bytes.len() == 0);
} by {
    if bytes.len() == 0 { }
    else { }
}
