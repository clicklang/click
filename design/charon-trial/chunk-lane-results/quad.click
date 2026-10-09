verifying "quad.rs";

theorem quad_byte_observation(value: uint8) {
 ensures to_integer((uint32)value) == to_integer((int32)value) by {
  have 0 <= (int32)value by { simp(); }
  have (int32)value <= 255 by { simp(); }
  apply(int32_less_equal_to_integer(0, (int32)value));
  apply(int32_less_equal_to_integer((int32)value, 255));
  arithmetic_certificate special {
   premise 0: 0 <= to_integer((int32)value) => 0 <= to_integer((int32)value);
   premise 1: to_integer((int32)value) <= 255 => to_integer((int32)value) <= 255;
   integer_cast_identity bounds [0, 1] => to_integer((uint32)value) == to_integer((int32)value);
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
 ensures to_integer(result.lanes[0]) == old(to_integer((int32)bytes[0]));
 ensures to_integer(result.lanes[1]) == old(to_integer((int32)bytes[1]));
 ensures to_integer(result.lanes[2]) == old(to_integer((int32)bytes[2]));
 ensures to_integer(result.lanes[3]) == old(to_integer((int32)bytes[3]));
} by {
 apply(quad_byte_observation(bytes[0]));
 apply(quad_byte_observation(bytes[1]));
 apply(quad_byte_observation(bytes[2]));
 apply(quad_byte_observation(bytes[3]));
 execute();
 have result.lanes[0] == old((uint32)bytes[0]) by { simp(); }
 have to_integer(result.lanes[0]) == old(to_integer((int32)bytes[0])) by { rewrite(result.lanes[0] == old((uint32)bytes[0])); assumption(); }
 have result.lanes[1] == old((uint32)bytes[1]) by { simp(); }
 have to_integer(result.lanes[1]) == old(to_integer((int32)bytes[1])) by { rewrite(result.lanes[1] == old((uint32)bytes[1])); assumption(); }
 have result.lanes[2] == old((uint32)bytes[2]) by { simp(); }
 have to_integer(result.lanes[2]) == old(to_integer((int32)bytes[2])) by { rewrite(result.lanes[2] == old((uint32)bytes[2])); assumption(); }
 have result.lanes[3] == old((uint32)bytes[3]) by { simp(); }
 have to_integer(result.lanes[3]) == old(to_integer((int32)bytes[3])) by { rewrite(result.lanes[3] == old((uint32)bytes[3])); assumption(); }
 simp();
}
fn quad::walk(bytes: &[u8]) -> u32 {
    requires bytes.len() == 16u64;
    views bytes[0..16];
    ensures result == 0u32;
} by {
    execute_until(loop(0));
    have viewable(bytes[0..16]) by {
        transport(at(function.entry, viewable(bytes[0..16])), viewable(bytes[0..16])) using { at(function.entry, viewable(bytes[0..16])); }
    }
    have __rust_mir_6_remaining == 16u64 by { simp(); }
    have 16u64 - __rust_mir_6_remaining == 0u64 by { rewrite(__rust_mir_6_remaining == 16u64); simp(); }
    have __rust_mir_6_cursor == bytes + (16u64 - __rust_mir_6_remaining) by { rewrite(16u64 - __rust_mir_6_remaining == 0u64); simp(); }
    loop {
        decreases __rust_mir_6_remaining;
        views bytes[0..16];
        invariant bytes.len() == 16u64;
        invariant viewable(bytes[0..16]);
        invariant __rust_mir_6_size == 4u64;
        invariant __rust_mir_6_remaining <= 16u64;
        invariant __rust_mir_6_remaining % 4u64 == 0u64;
        invariant __rust_mir_6_cursor == bytes + (16u64 - __rust_mir_6_remaining);
        preserve by {
            have 4u64 <= __rust_mir_6_remaining by { simp(); }
            have (16u64 - __rust_mir_6_remaining) + 4u64 <= 16u64 by { arithmetic() using { __rust_mir_6_remaining <= 16u64; 4u64 <= __rust_mir_6_remaining; } }
            have 16u64 - __rust_mir_6_remaining <= 12u64 by { arithmetic() using { 4u64 <= __rust_mir_6_remaining; __rust_mir_6_remaining <= 16u64; } }
            mark iteration;
            execute_until(assignment(chunk, 0)); step();
            execute_until(assignment(_byte, 0));
            have lanes.lanes[0] == chunk[0] by { simp(); }
            have lanes.lanes[1] == chunk[1] by { simp(); }
            have lanes.lanes[2] == chunk[2] by { simp(); }
            have lanes.lanes[3] == chunk[3] by { simp(); }

            have lanes.lanes[0] == (uint32)chunk[0] by { simp(); }
            have to_integer(lanes.lanes[0]) == to_integer((int32)chunk[0]) by { rewrite(lanes.lanes[0] == (uint32)chunk[0]); apply(quad_byte_observation(chunk[0])); assumption(); }
            have lanes.lanes[1] == (uint32)chunk[1] by { simp(); }
            have to_integer(lanes.lanes[1]) == to_integer((int32)chunk[1]) by { rewrite(lanes.lanes[1] == (uint32)chunk[1]); apply(quad_byte_observation(chunk[1])); assumption(); }
            have lanes.lanes[2] == (uint32)chunk[2] by { simp(); }
            have to_integer(lanes.lanes[2]) == to_integer((int32)chunk[2]) by { rewrite(lanes.lanes[2] == (uint32)chunk[2]); apply(quad_byte_observation(chunk[2])); assumption(); }
            have lanes.lanes[3] == (uint32)chunk[3] by { simp(); }
            have to_integer(lanes.lanes[3]) == to_integer((int32)chunk[3]) by { rewrite(lanes.lanes[3] == (uint32)chunk[3]); apply(quad_byte_observation(chunk[3])); assumption(); }
            execute_until(back_edge());
            have viewable(bytes[0..16]) by {
                transport(at(iteration, viewable(bytes[0..16])), viewable(bytes[0..16])) using { at(iteration, viewable(bytes[0..16])); }
            }
            have __rust_mir_6_remaining == at(iteration, __rust_mir_6_remaining) - 4u64 by { simp(); }
            have (at(iteration, __rust_mir_6_remaining) - 4u64) % 4u64 == at(iteration, __rust_mir_6_remaining % 4u64) by {
                normalize() using { 4u64 <= at(iteration, __rust_mir_6_remaining); }
            }
            have __rust_mir_6_remaining % 4u64 == 0u64 by {
                rewrite(__rust_mir_6_remaining == at(iteration, __rust_mir_6_remaining) - 4u64);
                rewrite((at(iteration, __rust_mir_6_remaining) - 4u64) % 4u64 == at(iteration, __rust_mir_6_remaining % 4u64)); simp();
            }
            have __rust_mir_6_remaining <= 16u64 by {
                arithmetic() using { __rust_mir_6_remaining == at(iteration, __rust_mir_6_remaining) - 4u64; 4u64 <= at(iteration, __rust_mir_6_remaining); at(iteration, __rust_mir_6_remaining) <= 16u64; }
            }
            have at(iteration, __rust_mir_6_cursor) + 4 == bytes + ((16u64 - at(iteration, __rust_mir_6_remaining)) + 4u64) by {
                arithmetic() using {
                    at(iteration, __rust_mir_6_cursor) == bytes + (16u64 - at(iteration, __rust_mir_6_remaining));
                    16u64 - at(iteration, __rust_mir_6_remaining) <= 12u64;
                }
            }
            have 16u64 - __rust_mir_6_remaining == (16u64 - at(iteration, __rust_mir_6_remaining)) + 4u64 by {
                arithmetic() using { __rust_mir_6_remaining == at(iteration, __rust_mir_6_remaining) - 4u64; 4u64 <= at(iteration, __rust_mir_6_remaining); at(iteration, __rust_mir_6_remaining) <= 16u64; }
            }
            have __rust_mir_6_cursor == bytes + (16u64 - __rust_mir_6_remaining) by {
                rewrite(16u64 - __rust_mir_6_remaining == (16u64 - at(iteration, __rust_mir_6_remaining)) + 4u64); simp();
            }
            have __rust_mir_6_remaining < at(iteration, __rust_mir_6_remaining) by {
                arithmetic() using { __rust_mir_6_remaining == at(iteration, __rust_mir_6_remaining) - 4u64; 4u64 <= at(iteration, __rust_mir_6_remaining); }
            }
            close_invariants();
        }
    }
    execute(); simp();
}
