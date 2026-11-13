import click::rust::slice;
import click::rust::chunks_exact;
import click::integer;

verifying "quad.rs";

theorem quad_byte_observation(value: uint8) {
 ensures to_integer(value as uint32) == to_integer(value as int32) by {
  have 0 <= value as int32;
  have value as int32 <= 255;
  apply(integer::int32_less_equal_to_integer(0, value as int32));
  apply(integer::int32_less_equal_to_integer(value as int32, 255));
  arithmetic_certificate rules {
   premise 0: 0 <= to_integer(value as int32) => 0 <= to_integer(value as int32);
   premise 1: to_integer(value as int32) <= 255 => to_integer(value as int32) <= 255;
   integer_cast_identity bounds [0, 1] => to_integer(value as uint32) == to_integer(value as int32);
   conclusion 0;
  }
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
 have to_integer(result.lanes[0]) == old(to_integer(bytes[0] as int32)) by { rewrite(result.lanes[0] == old(bytes[0] as uint32)); assumption(); }
 have result.lanes[1] == old(bytes[1] as uint32);
 have to_integer(result.lanes[1]) == old(to_integer(bytes[1] as int32)) by { rewrite(result.lanes[1] == old(bytes[1] as uint32)); assumption(); }
 have result.lanes[2] == old(bytes[2] as uint32);
 have to_integer(result.lanes[2]) == old(to_integer(bytes[2] as int32)) by { rewrite(result.lanes[2] == old(bytes[2] as uint32)); assumption(); }
 have result.lanes[3] == old(bytes[3] as uint32);
 have to_integer(result.lanes[3]) == old(to_integer(bytes[3] as int32)) by { rewrite(result.lanes[3] == old(bytes[3] as uint32)); assumption(); }
 solve();
}
fn quad::walk(bytes: &[u8]) -> u32 {
    requires bytes.len() == 16u64;
    views bytes[0..16];
    ensures result == 0u32;
} by {
    step_until(loop(0));
    have loop(0).iter == chunks_exact::chunks_exact(Slice<u8>::Slice(bytes, bytes.len()), 4u64);
    have loop(0).iter.len() == bytes.len() / 4u64 by {
        apply(chunks_exact::len_chunks_exact(Slice<u8>::Slice(bytes, bytes.len()), 4u64));
        solve();
    }
    loop {
        decreases iter.len();
        views bytes[0..16];
        invariant bytes.len() == 16u64;
        invariant iter == chunks_exact::after(chunks_exact::chunks_exact(Slice<u8>::Slice(bytes, bytes.len()), 4u64), iterations);
        invariant to_integer(iter.len()) + iterations == to_integer(bytes.len() / 4u64);
        initialize by {
            have bytes.len() == 16u64;
            have iter == chunks_exact::after(chunks_exact::chunks_exact(Slice<u8>::Slice(bytes, bytes.len()), 4u64), iterations) by {
                apply(chunks_exact::after_zero(chunks_exact::chunks_exact(Slice<u8>::Slice(bytes, bytes.len()), 4u64)));
                have iter == chunks_exact::chunks_exact(Slice<u8>::Slice(bytes, bytes.len()), 4u64);
                solve();
            }
            have to_integer(iter.len()) + iterations == to_integer(bytes.len() / 4u64);
        }
        preserve by {
            if 0u64 < iter.len() {
                have chunks_exact::chunks_exact(Slice<u8>::Slice(bytes, bytes.len()), 4u64).len() == bytes.len() / 4u64 by {
                    apply(chunks_exact::len_chunks_exact(Slice<u8>::Slice(bytes, bytes.len()), 4u64));
                }
                have iter.len() <= bytes.len() / 4u64;
                have to_integer((bytes.len() / 4u64 - iter.len())) == iterations;
                have (bytes.len() / 4u64 - iter.len()) < chunks_exact::chunks_exact(Slice<u8>::Slice(bytes, bytes.len()), 4u64).len();
                have iter.nth(0u64) == chunks_exact::chunks_exact(Slice<u8>::Slice(bytes, bytes.len()), 4u64).nth((bytes.len() / 4u64 - iter.len())) by {
                    apply(chunks_exact::nth_after(chunks_exact::chunks_exact(Slice<u8>::Slice(bytes, bytes.len()), 4u64), iterations, 0u64, (bytes.len() / 4u64 - iter.len())));
                    solve();
                }
                have iter.nth(0u64).len() == 4u64 by {
                    apply(chunks_exact::nth_chunks_exact(Slice<u8>::Slice(bytes, bytes.len()), 4u64, (bytes.len() / 4u64 - iter.len())));
                    solve();
                }
                have iter.nth(0u64).as_ptr() == bytes + (bytes.len() / 4u64 - iter.len()) * 4u64 by {
                    apply(chunks_exact::nth_chunks_exact(Slice<u8>::Slice(bytes, bytes.len()), 4u64, (bytes.len() / 4u64 - iter.len())));
                    solve();
                }
                have iter.after_next() == chunks_exact::after(chunks_exact::chunks_exact(Slice<u8>::Slice(bytes, bytes.len()), 4u64), iterations + 1) by {
                    apply(chunks_exact::after_next_after(chunks_exact::chunks_exact(Slice<u8>::Slice(bytes, bytes.len()), 4u64), iterations));
                    solve();
                }
                have iter.after_next().len() == iter.len() - 1u64 by {
                    apply(chunks_exact::len_after_next(iter));
                }
                have (bytes.len() / 4u64 - iter.len()) <= 3u64;
                have to_integer((bytes.len() / 4u64 - iter.len()) * 4u64) == to_integer((bytes.len() / 4u64 - iter.len())) * 4;
                have to_integer((bytes.len() / 4u64 - iter.len()) * 4u64) <= 12;
                have to_integer((bytes.len() / 4u64 - iter.len()) * 4u64 + 4u64) <= 16;
                mark taken;
                step_until(assignment(chunk, 0)); step(); step();
                have chunk == bytes + (bytes.len() / 4u64 - at(taken, iter.len())) * 4u64;
                have chunk_len == 4u64;
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
                have to_integer(lanes.lanes[0]) == to_integer(chunk[0] as int32) by { rewrite(lanes.lanes[0] == chunk[0] as uint32); apply(quad_byte_observation(chunk[0])); assumption(); }
                have lanes.lanes[1] == chunk[1] as uint32;
                have to_integer(lanes.lanes[1]) == to_integer(chunk[1] as int32) by { rewrite(lanes.lanes[1] == chunk[1] as uint32); apply(quad_byte_observation(chunk[1])); assumption(); }
                have lanes.lanes[2] == chunk[2] as uint32;
                have to_integer(lanes.lanes[2]) == to_integer(chunk[2] as int32) by { rewrite(lanes.lanes[2] == chunk[2] as uint32); apply(quad_byte_observation(chunk[2])); assumption(); }
                have lanes.lanes[3] == chunk[3] as uint32;
                have to_integer(lanes.lanes[3]) == to_integer(chunk[3] as int32) by { rewrite(lanes.lanes[3] == chunk[3] as uint32); apply(quad_byte_observation(chunk[3])); assumption(); }
                step_until(loop(0).back_edge());
                have iter == at(taken, iter.after_next());
                have iter.len() == at(taken, iter.len()) - 1u64;
                have 0u64 < at(taken, iter.len());
                have iter.len() < at(taken, iter.len());
            } else {
                have iter.len() == 0u64;
                step(); step(); step();
            }
        }
    }
    have loop(0).iter.len() == 0u64;
    step_until(function.exit);
    solve();
}
