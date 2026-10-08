verifying "quad.rs";
struct __rust_q_I4_quad_I4_Quad __rust_q_I4_quad_I4_load(const uint8* bytes, uint64 bytes_len) {
 requires bytes_len == 4u64; views bytes[0..4];
 ensures result.lanes[0] == bytes[0];
 ensures result.lanes[1] == bytes[1];
 ensures result.lanes[2] == bytes[2];
 ensures result.lanes[3] == bytes[3];
} by { execute(); simp(); }
uint32 __rust_q_I4_quad_I4_walk(const uint8* bytes, uint64 bytes_len) {
    requires bytes_len == 16u64;
    views bytes[0..16];
    ensures result == 0u32;
} by {
    execute_until(loop(0));
    have viewable(bytes[0..16]) by {
        transport(at(function.entry, viewable(bytes[0..16])), viewable(bytes[0..16])) using { at(function.entry, viewable(bytes[0..16])); }
    }
    have __rust_mir_6_remaining == 16 by { simp(); }
    have __rust_mir_6_cursor == bytes + (16 - __rust_mir_6_remaining) by { rewrite(__rust_mir_6_remaining == 16); simp(); }
    loop {
        decreases __rust_mir_6_remaining;
        views bytes[0..16];
        invariant bytes_len == 16u64;
        invariant viewable(bytes[0..16]);
        invariant __rust_mir_6_size == 4u64;
        invariant 0 <= __rust_mir_6_remaining and __rust_mir_6_remaining <= 16;
        invariant __rust_mir_6_remaining % 4 == 0;
        invariant __rust_mir_6_cursor == bytes + (16 - __rust_mir_6_remaining);
        preserve by {
            have 4 <= __rust_mir_6_remaining by { simp(); }
            have 0 <= 16 - __rust_mir_6_remaining by { arithmetic() using { 0 <= __rust_mir_6_remaining; __rust_mir_6_remaining <= 16; 4 <= __rust_mir_6_remaining; } }
            have (16 - __rust_mir_6_remaining) + 4 <= 16 by { arithmetic() using { 0 <= __rust_mir_6_remaining; __rust_mir_6_remaining <= 16; 4 <= __rust_mir_6_remaining; } }
            have 16 - __rust_mir_6_remaining <= 12 by { arithmetic() using { 4 <= __rust_mir_6_remaining; __rust_mir_6_remaining <= 16; } }
            mark iteration;
            execute_until(assignment(chunk, 0)); step();
            execute_until(assignment(_byte, 0));
            have lanes.lanes[0] == chunk[0] by { simp(); }
            have lanes.lanes[1] == chunk[1] by { simp(); }
            have lanes.lanes[2] == chunk[2] by { simp(); }
            have lanes.lanes[3] == chunk[3] by { simp(); }

            have array[0] == chunk[0] by { simp(); }
            have array[1] == chunk[1] by { simp(); }
            have array[2] == chunk[2] by { simp(); }
            have array[3] == chunk[3] by { simp(); }
            execute_until(back_edge());
            have viewable(bytes[0..16]) by {
                transport(at(iteration, viewable(bytes[0..16])), viewable(bytes[0..16])) using { at(iteration, viewable(bytes[0..16])); }
            }
            have __rust_mir_6_remaining == at(iteration, __rust_mir_6_remaining) - 4 by { simp(); }
            have (at(iteration, __rust_mir_6_remaining) - 4) % 4 == at(iteration, __rust_mir_6_remaining % 4) by {
                normalize() using { at(iteration, 4 <= __rust_mir_6_remaining); }
            }
            have __rust_mir_6_remaining % 4 == 0 by {
                rewrite(__rust_mir_6_remaining == at(iteration, __rust_mir_6_remaining) - 4);
                rewrite((at(iteration, __rust_mir_6_remaining) - 4) % 4 == at(iteration, __rust_mir_6_remaining % 4)); simp();
            }
            have 0 <= __rust_mir_6_remaining by {
                arithmetic() using { at(iteration, 4 <= __rust_mir_6_remaining); at(iteration, __rust_mir_6_remaining <= 16); __rust_mir_6_remaining == at(iteration, __rust_mir_6_remaining) - 4; }
            }
            have __rust_mir_6_remaining <= 16 by {
                arithmetic() using { at(iteration, 4 <= __rust_mir_6_remaining); at(iteration, __rust_mir_6_remaining <= 16); __rust_mir_6_remaining == at(iteration, __rust_mir_6_remaining) - 4; }
            }
            have __rust_mir_6_cursor == at(iteration, __rust_mir_6_cursor) + 4 by { simp(); }
            have 16 - __rust_mir_6_remaining == at(iteration, 16 - __rust_mir_6_remaining) + 4 by {
                arithmetic() using {
                    __rust_mir_6_remaining == at(iteration, __rust_mir_6_remaining) - 4;
                    at(iteration, 4 <= __rust_mir_6_remaining);
                    at(iteration, __rust_mir_6_remaining <= 16);
                }
            }
            have at(iteration, __rust_mir_6_cursor) + 4 == bytes + (at(iteration, 16 - __rust_mir_6_remaining) + 4) by {
                arithmetic() using {
                    at(iteration, __rust_mir_6_cursor == bytes + (16 - __rust_mir_6_remaining));
                    at(iteration, 0 <= 16 - __rust_mir_6_remaining);
                    at(iteration, 16 - __rust_mir_6_remaining <= 12);
                }
            }
            have __rust_mir_6_cursor == bytes + (16 - __rust_mir_6_remaining) by {
                rewrite(16 - __rust_mir_6_remaining == at(iteration, 16 - __rust_mir_6_remaining) + 4); simp();
            }
            close_invariants();
        }
    }
    execute(); simp();
}
