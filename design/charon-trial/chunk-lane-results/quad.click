import click::integer;

verifying "quad.rs";

theorem quad_byte_observation(value: uint8) {
 ensures to_integer(value as uint32) == to_integer(value as int32) by {
  have 0 <= value as int32;
  have value as int32 <= 255;
  apply(integer::int32_less_equal_to_integer(0, value as int32));
  apply(integer::int32_less_equal_to_integer(value as int32, 255));
  solve() using { 0 <= to_integer(value as int32); to_integer(value as int32) <= 255; };
 }
}
fn quad::load(bytes: &[u8]) -> quad::Quad {
 requires bytes.len() == 4u64; views bytes[0..4];
 ensures result.lanes[0] == bytes[0];
 ensures result.lanes[1] == bytes[1];
 ensures result.lanes[2] == bytes[2];
 ensures result.lanes[3] == bytes[3];
 ensures to_integer(result.lanes[0]) == old(to_integer(bytes[0] as int32));
 ensures to_integer(result.lanes[1]) == old(to_integer(bytes[1] as int32));
 ensures to_integer(result.lanes[2]) == old(to_integer(bytes[2] as int32));
 ensures to_integer(result.lanes[3]) == old(to_integer(bytes[3] as int32));
} by {
 apply(quad_byte_observation(bytes[0]));
 apply(quad_byte_observation(bytes[1]));
 apply(quad_byte_observation(bytes[2]));
 apply(quad_byte_observation(bytes[3]));
 step_until(function.exit);
 have result.lanes[0] == old(bytes[0] as uint32);
 have to_integer(result.lanes[0]) == old(to_integer(bytes[0] as int32)) by { rewrite(result.lanes[0], old(bytes[0] as uint32)); known(); }
 have result.lanes[1] == old(bytes[1] as uint32);
 have to_integer(result.lanes[1]) == old(to_integer(bytes[1] as int32)) by { rewrite(result.lanes[1], old(bytes[1] as uint32)); known(); }
 have result.lanes[2] == old(bytes[2] as uint32);
 have to_integer(result.lanes[2]) == old(to_integer(bytes[2] as int32)) by { rewrite(result.lanes[2], old(bytes[2] as uint32)); known(); }
 have result.lanes[3] == old(bytes[3] as uint32);
 have to_integer(result.lanes[3]) == old(to_integer(bytes[3] as int32)) by { rewrite(result.lanes[3], old(bytes[3] as uint32)); known(); }
 solve();
}
fn quad::walk(bytes: &[u8]) -> u32 {
    requires bytes.len() == 16u64;
    views bytes[0..16];
    ensures result == 0u32;
} by {
    step_until(loop(0));
    loop {
        decreases iter.v.len();
        views bytes[0..16];
        invariant bytes.len() == 16u64;
        invariant iter.chunk_size == 4u64;
        invariant iter.v.len() <= 16u64;
        invariant iter.v == bytes + (16u64 - iter.v.len());
        preserve by {
            if 4u64 <= iter.v.len() {
                have to_integer(16u64 - iter.v.len()) + 4 <= 16;
                have to_integer((16u64 - iter.v.len()) + 4u64) <= 16;
                have to_integer(16u64 - iter.v.len()) < 16;
                have to_integer(16u64 - iter.v.len()) + 4 <= 18446744073709551615;
                have (bytes + (16u64 - iter.v.len())) + 4u64 == bytes + ((16u64 - iter.v.len()) + 4u64);
                mark taken;
                step_until(assignment(chunk, 0)); step(); step();
                have chunk == bytes + (16u64 - at(taken, iter.v.len()));
                have chunk.len() == 4u64;
                mark before;
                step_until(assignment(_byte, 0));
                have lanes.lanes[0] == at(before, chunk[0]);
                have lanes.lanes[0] == chunk[0];
                have lanes.lanes[1] == at(before, chunk[1]);
                have lanes.lanes[1] == chunk[1];
                have lanes.lanes[2] == at(before, chunk[2]);
                have lanes.lanes[2] == chunk[2];
                have lanes.lanes[3] == at(before, chunk[3]);
                have lanes.lanes[3] == chunk[3];

                have lanes.lanes[0] == chunk[0] as uint32;
                have to_integer(lanes.lanes[0]) == to_integer(chunk[0] as int32) by { rewrite(lanes.lanes[0], chunk[0] as uint32); apply(quad_byte_observation(chunk[0])); known(); }
                have lanes.lanes[1] == chunk[1] as uint32;
                have to_integer(lanes.lanes[1]) == to_integer(chunk[1] as int32) by { rewrite(lanes.lanes[1], chunk[1] as uint32); apply(quad_byte_observation(chunk[1])); known(); }
                have lanes.lanes[2] == chunk[2] as uint32;
                have to_integer(lanes.lanes[2]) == to_integer(chunk[2] as int32) by { rewrite(lanes.lanes[2], chunk[2] as uint32); apply(quad_byte_observation(chunk[2])); known(); }
                have lanes.lanes[3] == chunk[3] as uint32;
                have to_integer(lanes.lanes[3]) == to_integer(chunk[3] as int32) by { rewrite(lanes.lanes[3], chunk[3] as uint32); apply(quad_byte_observation(chunk[3])); known(); }
                step_until(loop(0).back_edge());
                have 4u64 <= at(taken, iter.v.len());
                have to_integer(iter.v.len()) == to_integer(at(taken, iter.v.len())) - 4;
                have (16u64 - at(taken, iter.v.len())) + 4u64 == 16u64 - iter.v.len();
                have iter.v == bytes + (16u64 - iter.v.len());
            } else {
                step(); step(); step();
            }
        }
    }
    step_until(function.exit);
    solve();
}
