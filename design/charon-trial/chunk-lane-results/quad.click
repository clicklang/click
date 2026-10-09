verifying "quad.rs";
fn quad::load(bytes: &[u8]) -> quad::Quad {
 requires bytes.len() == 4u64; views bytes[0..4];
 ensures result.lanes[0] == bytes[0];
 ensures result.lanes[1] == bytes[1];
 ensures result.lanes[2] == bytes[2];
 ensures result.lanes[3] == bytes[3];
} by { execute(); simp(); }
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
