import click::integer;

verifying "borrow.rs";
theorem byte_reflexive(value: uint8) { ensures value == value by { close(); } }

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

fn increment_first(bytes: &mut [u8]) {
    requires bytes.len() == 4;
    requires bytes[0] < 255;
    owns bytes[0..4];
    ensures bytes[0] == old(bytes[0]) + 1;
} by {
    step_until(function.exit);
    have to_integer(old(bytes[0])) < 255 by { close(); }
    apply(integer::lt_step_le(to_integer(old(bytes[0])), 255));
    have 0 <= to_integer(old(bytes[0])) + 1 by { close(); }
    apply(integer::to_uint8_round_trip(to_integer(old(bytes[0])) + 1));
    have bytes[0] == old(bytes[0]) + 1 by {
        apply(byte_reflexive(to_uint8(to_integer(old(bytes[0])) + 1)));
        close();
    }
    close();
}

fn empty(bytes: &[u8]) -> bool {
    ensures result == (bytes.len() == 0);
} by {
    if bytes.len() == 0 { step_until(function.exit); close(); }
    else { step_until(function.exit); close(); }
}
