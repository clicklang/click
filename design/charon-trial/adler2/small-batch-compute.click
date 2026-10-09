# Original compute bounds for small batches divisible by four and canonical seeds.
# Length is at most 22204 bytes; both initial fields are below MOD = 65521.
# The two remainder conditions retain unsigned metadata and signed index spellings.
# Outer batches, short tails, and a checksum specification remain separate work.
# Verification assembles this contract with helpers, recombination, and iterator bounds.

theorem adler_uint64_self_subtract(n: uint64) { ensures n - n == 0u64 by { normalize(); } }
theorem adler_i32_below_mod(n: int32) { requires n <= 65520; ensures n < 65521 by { arithmetic() using { n <= 65520; } } }
theorem adler_bounded_pointer_association(base: const uint8*, index: int32) {
 requires 0 <= index;
 requires index <= 22200;
 ensures (base + index) + 4 == base + (index + 4) by {
  have defined(index + 4) by { simp() using { 0 <= index; index <= 22200; } }
  normalize() using { defined(index + 4); }
 }
}
theorem adler_scalar_batch_product_bound(length: uint32, seed: uint32) {
 requires length <= 22204u32;
 requires seed <= 65520u32;
 ensures to_integer(length) * to_integer(seed) <= 1454806080 by {
  apply(uint32_to_integer_bounds(length));
  apply(uint32_to_integer_bounds(seed));
  apply(uint32_less_equal_to_integer(length, 22204u32)) using { length <= 22204u32; }
  apply(uint32_less_equal_to_integer(seed, 65520u32)) using { seed <= 65520u32; }
  arithmetic_certificate special {
   premise 0: 0 <= to_integer(length) => 0 <= to_integer(length);
   premise 1: to_integer(length) <= 22204 => to_integer(length) <= 22204;
   premise 2: 0 <= to_integer(seed) => 0 <= to_integer(seed);
   premise 3: to_integer(seed) <= 65520 => to_integer(seed) <= 65520;
   integer_product_bounds bounds [0, 1, 2, 3] => to_integer(length) * to_integer(seed) <= 1454806080;
   conclusion 0;
  }
 }
}
theorem adler_small_length_cast(length: uint64) {
 requires length <= 22204u64;
 ensures (uint32)length <= 22204u32 by {
  have 0u64 <= length by { normalize(); }
  apply(uint64_less_equal_to_integer(0u64, length)) using { 0u64 <= length; }
  apply(uint64_less_equal_to_integer(length, 22204u64)) using { length <= 22204u64; }
  have 0 <= to_integer(length) by { assumption(); }
  have to_integer(length) <= 4294967295 by { arithmetic() using { to_integer(length) <= 22204; } }
  have to_integer((uint32)length) == to_integer(length) by {
   arithmetic_certificate special {
    premise 0: 0 <= to_integer(length) => 0 <= to_integer(length);
    premise 1: to_integer(length) <= 4294967295 => to_integer(length) <= 4294967295;
    integer_cast_identity bounds [0, 1] => to_integer((uint32)length) == to_integer(length);
    conclusion 0;
   }
  }
  have to_integer((uint32)length) <= to_integer(22204u32) by { rewrite(to_integer((uint32)length) == to_integer(length)); assumption(); }
  apply(uint32_less_equal_of_to_integer((uint32)length, 22204u32)) using { to_integer((uint32)length) <= to_integer(22204u32); }
 }
}
void __rust_q_I6_adler2_I4_algo_T29___rust_q_I6_adler2_I7_Adler32_I7_compute(struct __rust_q_I6_adler2_I7_Adler32* self, const uint8* bytes, uint64 bytes_len) {
 requires bytes_len <= 22204u64;
 requires bytes_len < 22208u64;
 requires bytes_len % 4u64 == 0u64;
 requires ((int32)(uint32)bytes_len) % 4 == 0;
 requires (uint32)self->a <= 65520u32;
 requires (uint32)self->b <= 65520u32;
 owns self->a;
 owns self->b;
 views bytes[0..(int32)(uint32)bytes_len];
 ensures self->a < 65521;
 ensures self->b < 65521;
} by {
 have viewable(bytes[0..(int32)(uint32)bytes_len]) by { assumption(); }
 have bytes_len <= 2147483647u64 by { normalize() using { bytes_len <= 22204u64; } }
 have 0 <= old((int32)(uint32)bytes_len) by { normalize() using { bytes_len <= 2147483647u64; } }
 have old((int32)(uint32)bytes_len) <= 22204 by { normalize() using { bytes_len <= 22204u64; } }
 have old((int32)(uint32)bytes_len) % 4 == 0 by { simp() using { ((int32)(uint32)bytes_len) % 4 == 0; } }
 have bytes_len - bytes_len % 4u64 == bytes_len by { rewrite(bytes_len % 4u64 == 0u64); simp() using {}; }
 have bytes_len % 4u64 <= bytes_len by { normalize(); }
 have bytes_len - bytes_len % 4u64 <= bytes_len by { normalize() using { bytes_len % 4u64 <= bytes_len; } }
 have bytes_len - bytes_len % 4u64 <= 2147483647u64 by { normalize() using { bytes_len - bytes_len % 4u64 <= bytes_len; bytes_len <= 2147483647u64; } }
 apply(uint64_less_equal_to_integer(bytes_len, 22204u64)) using { bytes_len <= 22204u64; }
 have bytes_len < 22208u64 by { assumption(); }
 have bytes_len % 22208u64 == bytes_len by { normalize() using { bytes_len < 22208u64; } }
 execute_until(assignment(b, 0)); step();
 have a == old((uint32)self->a) by { simp(); }
 have a <= 65520u32 by { rewrite(a == old((uint32)self->a)); assumption(); }
 have b == old((uint32)self->b) by { simp(); }
 have b <= 65520u32 by { rewrite(b == old((uint32)self->b)); assumption(); }
 execute_until(assignment(remainder_chunk_len, 0)); step();
 have (int32)(uint32)remainder_chunk_len == old((int32)(uint32)bytes_len) by { simp(); }
 execute_until(loop(0));
 have __rust_mir_27_size == 22208u64 by { simp(); }
 have __rust_mir_10_len == bytes_len by { simp(); }
 have __rust_mir_27_remaining == (int32)(uint32)(__rust_mir_10_len - __rust_mir_10_len % 22208u64) by { simp(); }
 have __rust_mir_27_remaining == 0 by { rewrite(__rust_mir_27_remaining == (int32)(uint32)(__rust_mir_10_len - __rust_mir_10_len % 22208u64)); rewrite(__rust_mir_10_len == bytes_len); rewrite(bytes_len % 22208u64 == bytes_len); apply(adler_uint64_self_subtract(bytes_len)); simp(); }
 have remainder_chunk_len == bytes_len by { simp(); }
 apply(uint64_less_equal_to_integer(bytes_len, 2147483647u64)) using { bytes_len <= 2147483647u64; }
 have to_integer(remainder_chunk_len) == to_integer(bytes_len) by { rewrite(remainder_chunk_len == bytes_len); normalize(); }
 have to_integer(remainder_chunk_len) <= to_integer(2147483647u64) by { rewrite(to_integer(remainder_chunk_len) == to_integer(bytes_len)); assumption(); }
 apply(uint64_less_equal_of_to_integer(remainder_chunk_len, 2147483647u64)) using { to_integer(remainder_chunk_len) <= to_integer(2147483647u64); }
 have remainder_chunk_len % 4u64 == 0u64 by { rewrite(remainder_chunk_len == bytes_len); assumption(); }
 execute_until(loop(2));
 have __rust_mir_62_remaining == old((int32)(uint32)bytes_len) by { simp(); }
 have __rust_mir_62_cursor == old(bytes) by { simp(); }
 have __rust_mir_62_size == 4u64 by { simp(); }
 have viewable(bytes[0..(int32)(uint32)bytes_len]) by { transport(at(function.entry, viewable(bytes[0..(int32)(uint32)bytes_len])), viewable(bytes[0..(int32)(uint32)bytes_len])) using { at(function.entry, viewable(bytes[0..(int32)(uint32)bytes_len])); 0 <= old((int32)(uint32)bytes_len); } }
 apply(adler_lane_initial_ceiling());
 apply(adler_lane_iterator_initial(old((int32)(uint32)bytes_len)));
 have adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), __rust_mir_62_remaining) == 0 by { rewrite(__rust_mir_62_remaining == old((int32)(uint32)bytes_len)); assumption(); }
 have to_integer(a_vec._0[0]) == 0 by { simp(); }
 have to_integer(a_vec._0[0]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), __rust_mir_62_remaining)) by { rewrite(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), __rust_mir_62_remaining) == 0); rewrite(adler_lane_a_ceiling(0) == 65520); arithmetic() using { to_integer(a_vec._0[0]) == 0; } }
 have to_integer(b_vec._0[0]) == 0 by { simp(); }
 have to_integer(b_vec._0[0]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), __rust_mir_62_remaining)) by { rewrite(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), __rust_mir_62_remaining) == 0); rewrite(adler_lane_b_ceiling(0) == 65520); arithmetic() using { to_integer(b_vec._0[0]) == 0; } }
 have to_integer(a_vec._0[1]) == 0 by { simp(); }
 have to_integer(a_vec._0[1]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), __rust_mir_62_remaining)) by { rewrite(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), __rust_mir_62_remaining) == 0); rewrite(adler_lane_a_ceiling(0) == 65520); arithmetic() using { to_integer(a_vec._0[1]) == 0; } }
 have to_integer(b_vec._0[1]) == 0 by { simp(); }
 have to_integer(b_vec._0[1]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), __rust_mir_62_remaining)) by { rewrite(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), __rust_mir_62_remaining) == 0); rewrite(adler_lane_b_ceiling(0) == 65520); arithmetic() using { to_integer(b_vec._0[1]) == 0; } }
 have to_integer(a_vec._0[2]) == 0 by { simp(); }
 have to_integer(a_vec._0[2]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), __rust_mir_62_remaining)) by { rewrite(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), __rust_mir_62_remaining) == 0); rewrite(adler_lane_a_ceiling(0) == 65520); arithmetic() using { to_integer(a_vec._0[2]) == 0; } }
 have to_integer(b_vec._0[2]) == 0 by { simp(); }
 have to_integer(b_vec._0[2]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), __rust_mir_62_remaining)) by { rewrite(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), __rust_mir_62_remaining) == 0); rewrite(adler_lane_b_ceiling(0) == 65520); arithmetic() using { to_integer(b_vec._0[2]) == 0; } }
 have to_integer(a_vec._0[3]) == 0 by { simp(); }
 have to_integer(a_vec._0[3]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), __rust_mir_62_remaining)) by { rewrite(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), __rust_mir_62_remaining) == 0); rewrite(adler_lane_a_ceiling(0) == 65520); arithmetic() using { to_integer(a_vec._0[3]) == 0; } }
 have to_integer(b_vec._0[3]) == 0 by { simp(); }
 have to_integer(b_vec._0[3]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), __rust_mir_62_remaining)) by { rewrite(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), __rust_mir_62_remaining) == 0); rewrite(adler_lane_b_ceiling(0) == 65520); arithmetic() using { to_integer(b_vec._0[3]) == 0; } }
 have 0 <= __rust_mir_62_remaining by { rewrite(__rust_mir_62_remaining == old((int32)(uint32)bytes_len)); assumption(); }
 have __rust_mir_62_remaining <= old((int32)(uint32)bytes_len) by { rewrite(__rust_mir_62_remaining == old((int32)(uint32)bytes_len)); normalize() using {}; }
 have 0 <= __rust_mir_62_remaining and __rust_mir_62_remaining <= old((int32)(uint32)bytes_len) by { assumption(); }
 have __rust_mir_62_remaining % 4 == 0 by { rewrite(__rust_mir_62_remaining == old((int32)(uint32)bytes_len)); assumption(); }
 have __rust_mir_62_cursor == old(bytes) + (old((int32)(uint32)bytes_len) - __rust_mir_62_remaining) by { rewrite(__rust_mir_62_remaining == old((int32)(uint32)bytes_len)); simp(); }
 loop {
  decreases __rust_mir_62_remaining;
  owns a_vec._0[0..4];
  owns b_vec._0[0..4];
  views bytes[0..(int32)(uint32)bytes_len];
  invariant viewable(bytes[0..(int32)(uint32)bytes_len]);
  invariant bytes_len <= 22204u64;
  invariant bytes_len < 22208u64;
  invariant bytes_len % 4u64 == 0u64;
  invariant bytes == old(bytes);
  invariant bytes_len == old(bytes_len);
  invariant a <= 65520u32;
  invariant b <= 65520u32;
  invariant 0 <= old((int32)(uint32)bytes_len);
  invariant old((int32)(uint32)bytes_len) <= 22204;
  invariant old((int32)(uint32)bytes_len) % 4 == 0;
  invariant __rust_mir_62_size == 4u64;
  invariant 0 <= __rust_mir_62_remaining and __rust_mir_62_remaining <= old((int32)(uint32)bytes_len);
  invariant __rust_mir_62_remaining % 4 == 0;
  invariant __rust_mir_62_cursor == old(bytes) + (old((int32)(uint32)bytes_len) - __rust_mir_62_remaining);
  invariant to_integer(a_vec._0[0]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), __rust_mir_62_remaining));
  invariant to_integer(b_vec._0[0]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), __rust_mir_62_remaining));
  invariant to_integer(a_vec._0[1]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), __rust_mir_62_remaining));
  invariant to_integer(b_vec._0[1]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), __rust_mir_62_remaining));
  invariant to_integer(a_vec._0[2]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), __rust_mir_62_remaining));
  invariant to_integer(b_vec._0[2]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), __rust_mir_62_remaining));
  invariant to_integer(a_vec._0[3]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), __rust_mir_62_remaining));
  invariant to_integer(b_vec._0[3]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), __rust_mir_62_remaining));
  preserve by {
   have 4 <= __rust_mir_62_remaining by { simp(); }
   mark lane_head;
   have at(lane_head, __rust_mir_62_remaining) % 4 == 0 by { simp(); }
   have at(lane_head, __rust_mir_62_remaining) <= old((int32)(uint32)bytes_len) by { simp(); }
   have 4 <= at(lane_head, __rust_mir_62_remaining) by { simp(); }
   have 0 <= at(lane_head, __rust_mir_62_remaining) by { simp(); }
   have old((int32)(uint32)bytes_len) <= 22208 by { arithmetic() using { old((int32)(uint32)bytes_len) <= 22204; } }
   have at(lane_head, viewable(bytes[0..(int32)(uint32)bytes_len])) by { simp() using { viewable(bytes[0..(int32)(uint32)bytes_len]); } }
   have at(lane_head, __rust_mir_62_cursor) == old(bytes) + (old((int32)(uint32)bytes_len) - at(lane_head, __rust_mir_62_remaining)) by { simp(); }
   have 0 <= old((int32)(uint32)bytes_len) - at(lane_head, __rust_mir_62_remaining) by { arithmetic() using { 0 <= old((int32)(uint32)bytes_len); old((int32)(uint32)bytes_len) <= 22204; 0 <= at(lane_head, __rust_mir_62_remaining); at(lane_head, __rust_mir_62_remaining) <= old((int32)(uint32)bytes_len); } }
   have (old((int32)(uint32)bytes_len) - at(lane_head, __rust_mir_62_remaining)) + 4 <= old((int32)(uint32)bytes_len) by { arithmetic() using { 0 <= old((int32)(uint32)bytes_len); old((int32)(uint32)bytes_len) <= 22204; 4 <= at(lane_head, __rust_mir_62_remaining); at(lane_head, __rust_mir_62_remaining) <= old((int32)(uint32)bytes_len); } }
   execute_until(assignment(__rust_mir_69, 0)); step();
   have __rust_mir_69 == at(lane_head, __rust_mir_62_cursor) by { simp(); }
   execute_until(assignment(__rust_mir_69_len, 0)); step();
   have __rust_mir_69_len == 4u64 by { simp(); }
   have __rust_mir_69 == old(bytes) + (old((int32)(uint32)bytes_len) - at(lane_head, __rust_mir_62_remaining)) by { rewrite(__rust_mir_69 == at(lane_head, __rust_mir_62_cursor)); assumption(); }
   have viewable(bytes[0..(int32)(uint32)bytes_len]) by { transport(at(lane_head, viewable(bytes[0..(int32)(uint32)bytes_len])), viewable(bytes[0..(int32)(uint32)bytes_len])) using { at(lane_head, viewable(bytes[0..(int32)(uint32)bytes_len])); bytes == old(bytes); bytes_len == old(bytes_len); 0 <= old((int32)(uint32)bytes_len); } }
   have __rust_mir_69 == bytes + (old((int32)(uint32)bytes_len) - at(lane_head, __rust_mir_62_remaining)) by { simp(); }
   have __rust_mir_62_remaining == at(lane_head, __rust_mir_62_remaining) - 4 by { simp(); }
   have (int32)(uint32)bytes_len - __rust_mir_62_remaining - 4 == old((int32)(uint32)bytes_len) - at(lane_head, __rust_mir_62_remaining) by { simp(); }
   have (int32)(uint32)bytes_len == old((int32)(uint32)bytes_len) by { simp(); }
   have 0 <= (int32)(uint32)bytes_len by { rewrite((int32)(uint32)bytes_len == old((int32)(uint32)bytes_len)); assumption(); }
   have (int32)(uint32)bytes_len <= 22204 by { rewrite((int32)(uint32)bytes_len == old((int32)(uint32)bytes_len)); assumption(); }
   have 0 <= (int32)(uint32)bytes_len - __rust_mir_62_remaining - 4 by { rewrite((int32)(uint32)bytes_len - __rust_mir_62_remaining - 4 == old((int32)(uint32)bytes_len) - at(lane_head, __rust_mir_62_remaining)); simp(); }
   have ((int32)(uint32)bytes_len - __rust_mir_62_remaining - 4) + 4 <= (int32)(uint32)bytes_len by { arithmetic() using { (int32)(uint32)bytes_len == old((int32)(uint32)bytes_len); __rust_mir_62_remaining == at(lane_head, __rust_mir_62_remaining) - 4; 0 <= old((int32)(uint32)bytes_len); old((int32)(uint32)bytes_len) <= 22204; 4 <= at(lane_head, __rust_mir_62_remaining); at(lane_head, __rust_mir_62_remaining) <= old((int32)(uint32)bytes_len); } }
   have (int32)(uint32)bytes_len - __rust_mir_62_remaining - 4 <= ((int32)(uint32)bytes_len - __rust_mir_62_remaining - 4) + 4 by { arithmetic() using { (int32)(uint32)bytes_len == old((int32)(uint32)bytes_len); __rust_mir_62_remaining == at(lane_head, __rust_mir_62_remaining) - 4; 0 <= old((int32)(uint32)bytes_len); old((int32)(uint32)bytes_len) <= 22204; 4 <= at(lane_head, __rust_mir_62_remaining); at(lane_head, __rust_mir_62_remaining) <= old((int32)(uint32)bytes_len); } }
   have viewable(bytes[((int32)(uint32)bytes_len - __rust_mir_62_remaining - 4)..((int32)(uint32)bytes_len - __rust_mir_62_remaining - 4) + 4]) by { transport(viewable(bytes[0..(int32)(uint32)bytes_len]), viewable(bytes[((int32)(uint32)bytes_len - __rust_mir_62_remaining - 4)..((int32)(uint32)bytes_len - __rust_mir_62_remaining - 4) + 4])) using { viewable(bytes[0..(int32)(uint32)bytes_len]); 0 <= ((int32)(uint32)bytes_len - __rust_mir_62_remaining - 4); ((int32)(uint32)bytes_len - __rust_mir_62_remaining - 4) <= ((int32)(uint32)bytes_len - __rust_mir_62_remaining - 4) + 4; ((int32)(uint32)bytes_len - __rust_mir_62_remaining - 4) + 4 <= (int32)(uint32)bytes_len; 0 <= (int32)(uint32)bytes_len; } }
   have __rust_mir_69 == bytes + ((int32)(uint32)bytes_len - __rust_mir_62_remaining - 4) by { simp(); }
   have viewable(__rust_mir_69[0..4]) by { rewrite(__rust_mir_69 == bytes + ((int32)(uint32)bytes_len - __rust_mir_62_remaining - 4)); simp() using { viewable(bytes[((int32)(uint32)bytes_len - __rust_mir_62_remaining - 4)..((int32)(uint32)bytes_len - __rust_mir_62_remaining - 4) + 4]); } }
   execute_until(assignment(__rust_mir_71, 0));
   have __rust_mir_62_remaining == at(lane_head, __rust_mir_62_remaining) - 4 by { simp(); }
   mark vector_a;
   apply(uint32_to_integer_bounds(at(vector_a, a_vec._0[0])));
   apply(uint32_to_integer_bounds(at(vector_a, b_vec._0[0])));
   apply(uint32_to_integer_bounds(at(vector_a, __rust_mir_68._0[0])));
   have 0 <= to_integer(at(vector_a, a_vec._0[0])) by { simp(); }
   have 0 <= to_integer(at(vector_a, b_vec._0[0])) by { simp(); }
   have to_integer(at(vector_a, a_vec._0[0])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), at(lane_head, __rust_mir_62_remaining))) by { simp(); }
   have to_integer(at(vector_a, b_vec._0[0])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), at(lane_head, __rust_mir_62_remaining))) by { simp(); }
   have 0 <= to_integer(at(vector_a, __rust_mir_68._0[0])) by { simp(); }
   have to_integer(at(vector_a, __rust_mir_68._0[0])) <= 255 by { simp(); }
   apply(adler_lane_iterator_add_contracts(old((int32)(uint32)bytes_len), at(lane_head, __rust_mir_62_remaining), at(vector_a, a_vec._0[0]), at(vector_a, b_vec._0[0]), at(vector_a, __rust_mir_68._0[0]))) using { 0 <= at(lane_head, __rust_mir_62_remaining); 4 <= at(lane_head, __rust_mir_62_remaining); at(lane_head, __rust_mir_62_remaining) <= old((int32)(uint32)bytes_len); old((int32)(uint32)bytes_len) <= 22208; 0 <= to_integer(at(vector_a, a_vec._0[0])); to_integer(at(vector_a, a_vec._0[0])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), at(lane_head, __rust_mir_62_remaining))); 0 <= to_integer(at(vector_a, b_vec._0[0])); to_integer(at(vector_a, b_vec._0[0])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), at(lane_head, __rust_mir_62_remaining))); 0 <= to_integer(at(vector_a, __rust_mir_68._0[0])); to_integer(at(vector_a, __rust_mir_68._0[0])) <= 255; }
   apply(adler_lane_iterator_native_preservation(old((int32)(uint32)bytes_len), at(lane_head, __rust_mir_62_remaining), at(vector_a, a_vec._0[0]), at(vector_a, b_vec._0[0]), at(vector_a, __rust_mir_68._0[0]))) using { 0 <= at(lane_head, __rust_mir_62_remaining); 4 <= at(lane_head, __rust_mir_62_remaining); at(lane_head, __rust_mir_62_remaining) <= old((int32)(uint32)bytes_len); old((int32)(uint32)bytes_len) <= 22208; 0 <= to_integer(at(vector_a, a_vec._0[0])); to_integer(at(vector_a, a_vec._0[0])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), at(lane_head, __rust_mir_62_remaining))); 0 <= to_integer(at(vector_a, b_vec._0[0])); to_integer(at(vector_a, b_vec._0[0])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), at(lane_head, __rust_mir_62_remaining))); 0 <= to_integer(at(vector_a, __rust_mir_68._0[0])); to_integer(at(vector_a, __rust_mir_68._0[0])) <= 255; }
   apply(uint32_to_integer_bounds(at(vector_a, a_vec._0[1])));
   apply(uint32_to_integer_bounds(at(vector_a, b_vec._0[1])));
   apply(uint32_to_integer_bounds(at(vector_a, __rust_mir_68._0[1])));
   have 0 <= to_integer(at(vector_a, a_vec._0[1])) by { simp(); }
   have 0 <= to_integer(at(vector_a, b_vec._0[1])) by { simp(); }
   have to_integer(at(vector_a, a_vec._0[1])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), at(lane_head, __rust_mir_62_remaining))) by { simp(); }
   have to_integer(at(vector_a, b_vec._0[1])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), at(lane_head, __rust_mir_62_remaining))) by { simp(); }
   have 0 <= to_integer(at(vector_a, __rust_mir_68._0[1])) by { simp(); }
   have to_integer(at(vector_a, __rust_mir_68._0[1])) <= 255 by { simp(); }
   apply(adler_lane_iterator_add_contracts(old((int32)(uint32)bytes_len), at(lane_head, __rust_mir_62_remaining), at(vector_a, a_vec._0[1]), at(vector_a, b_vec._0[1]), at(vector_a, __rust_mir_68._0[1]))) using { 0 <= at(lane_head, __rust_mir_62_remaining); 4 <= at(lane_head, __rust_mir_62_remaining); at(lane_head, __rust_mir_62_remaining) <= old((int32)(uint32)bytes_len); old((int32)(uint32)bytes_len) <= 22208; 0 <= to_integer(at(vector_a, a_vec._0[1])); to_integer(at(vector_a, a_vec._0[1])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), at(lane_head, __rust_mir_62_remaining))); 0 <= to_integer(at(vector_a, b_vec._0[1])); to_integer(at(vector_a, b_vec._0[1])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), at(lane_head, __rust_mir_62_remaining))); 0 <= to_integer(at(vector_a, __rust_mir_68._0[1])); to_integer(at(vector_a, __rust_mir_68._0[1])) <= 255; }
   apply(adler_lane_iterator_native_preservation(old((int32)(uint32)bytes_len), at(lane_head, __rust_mir_62_remaining), at(vector_a, a_vec._0[1]), at(vector_a, b_vec._0[1]), at(vector_a, __rust_mir_68._0[1]))) using { 0 <= at(lane_head, __rust_mir_62_remaining); 4 <= at(lane_head, __rust_mir_62_remaining); at(lane_head, __rust_mir_62_remaining) <= old((int32)(uint32)bytes_len); old((int32)(uint32)bytes_len) <= 22208; 0 <= to_integer(at(vector_a, a_vec._0[1])); to_integer(at(vector_a, a_vec._0[1])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), at(lane_head, __rust_mir_62_remaining))); 0 <= to_integer(at(vector_a, b_vec._0[1])); to_integer(at(vector_a, b_vec._0[1])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), at(lane_head, __rust_mir_62_remaining))); 0 <= to_integer(at(vector_a, __rust_mir_68._0[1])); to_integer(at(vector_a, __rust_mir_68._0[1])) <= 255; }
   apply(uint32_to_integer_bounds(at(vector_a, a_vec._0[2])));
   apply(uint32_to_integer_bounds(at(vector_a, b_vec._0[2])));
   apply(uint32_to_integer_bounds(at(vector_a, __rust_mir_68._0[2])));
   have 0 <= to_integer(at(vector_a, a_vec._0[2])) by { simp(); }
   have 0 <= to_integer(at(vector_a, b_vec._0[2])) by { simp(); }
   have to_integer(at(vector_a, a_vec._0[2])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), at(lane_head, __rust_mir_62_remaining))) by { simp(); }
   have to_integer(at(vector_a, b_vec._0[2])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), at(lane_head, __rust_mir_62_remaining))) by { simp(); }
   have 0 <= to_integer(at(vector_a, __rust_mir_68._0[2])) by { simp(); }
   have to_integer(at(vector_a, __rust_mir_68._0[2])) <= 255 by { simp(); }
   apply(adler_lane_iterator_add_contracts(old((int32)(uint32)bytes_len), at(lane_head, __rust_mir_62_remaining), at(vector_a, a_vec._0[2]), at(vector_a, b_vec._0[2]), at(vector_a, __rust_mir_68._0[2]))) using { 0 <= at(lane_head, __rust_mir_62_remaining); 4 <= at(lane_head, __rust_mir_62_remaining); at(lane_head, __rust_mir_62_remaining) <= old((int32)(uint32)bytes_len); old((int32)(uint32)bytes_len) <= 22208; 0 <= to_integer(at(vector_a, a_vec._0[2])); to_integer(at(vector_a, a_vec._0[2])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), at(lane_head, __rust_mir_62_remaining))); 0 <= to_integer(at(vector_a, b_vec._0[2])); to_integer(at(vector_a, b_vec._0[2])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), at(lane_head, __rust_mir_62_remaining))); 0 <= to_integer(at(vector_a, __rust_mir_68._0[2])); to_integer(at(vector_a, __rust_mir_68._0[2])) <= 255; }
   apply(adler_lane_iterator_native_preservation(old((int32)(uint32)bytes_len), at(lane_head, __rust_mir_62_remaining), at(vector_a, a_vec._0[2]), at(vector_a, b_vec._0[2]), at(vector_a, __rust_mir_68._0[2]))) using { 0 <= at(lane_head, __rust_mir_62_remaining); 4 <= at(lane_head, __rust_mir_62_remaining); at(lane_head, __rust_mir_62_remaining) <= old((int32)(uint32)bytes_len); old((int32)(uint32)bytes_len) <= 22208; 0 <= to_integer(at(vector_a, a_vec._0[2])); to_integer(at(vector_a, a_vec._0[2])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), at(lane_head, __rust_mir_62_remaining))); 0 <= to_integer(at(vector_a, b_vec._0[2])); to_integer(at(vector_a, b_vec._0[2])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), at(lane_head, __rust_mir_62_remaining))); 0 <= to_integer(at(vector_a, __rust_mir_68._0[2])); to_integer(at(vector_a, __rust_mir_68._0[2])) <= 255; }
   apply(uint32_to_integer_bounds(at(vector_a, a_vec._0[3])));
   apply(uint32_to_integer_bounds(at(vector_a, b_vec._0[3])));
   apply(uint32_to_integer_bounds(at(vector_a, __rust_mir_68._0[3])));
   have 0 <= to_integer(at(vector_a, a_vec._0[3])) by { simp(); }
   have 0 <= to_integer(at(vector_a, b_vec._0[3])) by { simp(); }
   have to_integer(at(vector_a, a_vec._0[3])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), at(lane_head, __rust_mir_62_remaining))) by { simp(); }
   have to_integer(at(vector_a, b_vec._0[3])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), at(lane_head, __rust_mir_62_remaining))) by { simp(); }
   have 0 <= to_integer(at(vector_a, __rust_mir_68._0[3])) by { simp(); }
   have to_integer(at(vector_a, __rust_mir_68._0[3])) <= 255 by { simp(); }
   apply(adler_lane_iterator_add_contracts(old((int32)(uint32)bytes_len), at(lane_head, __rust_mir_62_remaining), at(vector_a, a_vec._0[3]), at(vector_a, b_vec._0[3]), at(vector_a, __rust_mir_68._0[3]))) using { 0 <= at(lane_head, __rust_mir_62_remaining); 4 <= at(lane_head, __rust_mir_62_remaining); at(lane_head, __rust_mir_62_remaining) <= old((int32)(uint32)bytes_len); old((int32)(uint32)bytes_len) <= 22208; 0 <= to_integer(at(vector_a, a_vec._0[3])); to_integer(at(vector_a, a_vec._0[3])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), at(lane_head, __rust_mir_62_remaining))); 0 <= to_integer(at(vector_a, b_vec._0[3])); to_integer(at(vector_a, b_vec._0[3])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), at(lane_head, __rust_mir_62_remaining))); 0 <= to_integer(at(vector_a, __rust_mir_68._0[3])); to_integer(at(vector_a, __rust_mir_68._0[3])) <= 255; }
   apply(adler_lane_iterator_native_preservation(old((int32)(uint32)bytes_len), at(lane_head, __rust_mir_62_remaining), at(vector_a, a_vec._0[3]), at(vector_a, b_vec._0[3]), at(vector_a, __rust_mir_68._0[3]))) using { 0 <= at(lane_head, __rust_mir_62_remaining); 4 <= at(lane_head, __rust_mir_62_remaining); at(lane_head, __rust_mir_62_remaining) <= old((int32)(uint32)bytes_len); old((int32)(uint32)bytes_len) <= 22208; 0 <= to_integer(at(vector_a, a_vec._0[3])); to_integer(at(vector_a, a_vec._0[3])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), at(lane_head, __rust_mir_62_remaining))); 0 <= to_integer(at(vector_a, b_vec._0[3])); to_integer(at(vector_a, b_vec._0[3])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), at(lane_head, __rust_mir_62_remaining))); 0 <= to_integer(at(vector_a, __rust_mir_68._0[3])); to_integer(at(vector_a, __rust_mir_68._0[3])) <= 255; }
   execute_until(assignment(__rust_mir_74, 0));
   have a_vec._0[0] == at(vector_a, a_vec._0[0]) + at(vector_a, __rust_mir_68._0[0]) by { simp(); }
   have b_vec._0[0] == at(vector_a, b_vec._0[0]) by { simp(); }
   have to_integer(b_vec._0[0]) == to_integer(at(vector_a, b_vec._0[0])) by { simp() using { b_vec._0[0] == at(vector_a, b_vec._0[0]); } }
   have to_integer(a_vec._0[0]) == to_integer(at(vector_a, a_vec._0[0]) + at(vector_a, __rust_mir_68._0[0])) by { simp() using { a_vec._0[0] == at(vector_a, a_vec._0[0]) + at(vector_a, __rust_mir_68._0[0]); } }
   have to_integer(b_vec._0[0]) + to_integer(a_vec._0[0]) <= 4294967295 by { arithmetic() using { to_integer(b_vec._0[0]) == to_integer(at(vector_a, b_vec._0[0])); to_integer(a_vec._0[0]) == to_integer(at(vector_a, a_vec._0[0]) + at(vector_a, __rust_mir_68._0[0])); to_integer(at(vector_a, b_vec._0[0])) + to_integer(at(vector_a, a_vec._0[0]) + at(vector_a, __rust_mir_68._0[0])) <= 4294967295; } }
   have a_vec._0[1] == at(vector_a, a_vec._0[1]) + at(vector_a, __rust_mir_68._0[1]) by { simp(); }
   have b_vec._0[1] == at(vector_a, b_vec._0[1]) by { simp(); }
   have to_integer(b_vec._0[1]) == to_integer(at(vector_a, b_vec._0[1])) by { simp() using { b_vec._0[1] == at(vector_a, b_vec._0[1]); } }
   have to_integer(a_vec._0[1]) == to_integer(at(vector_a, a_vec._0[1]) + at(vector_a, __rust_mir_68._0[1])) by { simp() using { a_vec._0[1] == at(vector_a, a_vec._0[1]) + at(vector_a, __rust_mir_68._0[1]); } }
   have to_integer(b_vec._0[1]) + to_integer(a_vec._0[1]) <= 4294967295 by { arithmetic() using { to_integer(b_vec._0[1]) == to_integer(at(vector_a, b_vec._0[1])); to_integer(a_vec._0[1]) == to_integer(at(vector_a, a_vec._0[1]) + at(vector_a, __rust_mir_68._0[1])); to_integer(at(vector_a, b_vec._0[1])) + to_integer(at(vector_a, a_vec._0[1]) + at(vector_a, __rust_mir_68._0[1])) <= 4294967295; } }
   have a_vec._0[2] == at(vector_a, a_vec._0[2]) + at(vector_a, __rust_mir_68._0[2]) by { simp(); }
   have b_vec._0[2] == at(vector_a, b_vec._0[2]) by { simp(); }
   have to_integer(b_vec._0[2]) == to_integer(at(vector_a, b_vec._0[2])) by { simp() using { b_vec._0[2] == at(vector_a, b_vec._0[2]); } }
   have to_integer(a_vec._0[2]) == to_integer(at(vector_a, a_vec._0[2]) + at(vector_a, __rust_mir_68._0[2])) by { simp() using { a_vec._0[2] == at(vector_a, a_vec._0[2]) + at(vector_a, __rust_mir_68._0[2]); } }
   have to_integer(b_vec._0[2]) + to_integer(a_vec._0[2]) <= 4294967295 by { arithmetic() using { to_integer(b_vec._0[2]) == to_integer(at(vector_a, b_vec._0[2])); to_integer(a_vec._0[2]) == to_integer(at(vector_a, a_vec._0[2]) + at(vector_a, __rust_mir_68._0[2])); to_integer(at(vector_a, b_vec._0[2])) + to_integer(at(vector_a, a_vec._0[2]) + at(vector_a, __rust_mir_68._0[2])) <= 4294967295; } }
   have a_vec._0[3] == at(vector_a, a_vec._0[3]) + at(vector_a, __rust_mir_68._0[3]) by { simp(); }
   have b_vec._0[3] == at(vector_a, b_vec._0[3]) by { simp(); }
   have to_integer(b_vec._0[3]) == to_integer(at(vector_a, b_vec._0[3])) by { simp() using { b_vec._0[3] == at(vector_a, b_vec._0[3]); } }
   have to_integer(a_vec._0[3]) == to_integer(at(vector_a, a_vec._0[3]) + at(vector_a, __rust_mir_68._0[3])) by { simp() using { a_vec._0[3] == at(vector_a, a_vec._0[3]) + at(vector_a, __rust_mir_68._0[3]); } }
   have to_integer(b_vec._0[3]) + to_integer(a_vec._0[3]) <= 4294967295 by { arithmetic() using { to_integer(b_vec._0[3]) == to_integer(at(vector_a, b_vec._0[3])); to_integer(a_vec._0[3]) == to_integer(at(vector_a, a_vec._0[3]) + at(vector_a, __rust_mir_68._0[3])); to_integer(at(vector_a, b_vec._0[3])) + to_integer(at(vector_a, a_vec._0[3]) + at(vector_a, __rust_mir_68._0[3])) <= 4294967295; } }
   mark vector_b;
   execute_until(back_edge());
   have a_vec._0[0] == at(vector_a, a_vec._0[0]) + at(vector_a, __rust_mir_68._0[0]) by { simp(); }
   have b_vec._0[0] == at(vector_a, b_vec._0[0]) + (at(vector_a, a_vec._0[0]) + at(vector_a, __rust_mir_68._0[0])) by { simp(); }
   have to_integer(a_vec._0[0]) == to_integer(at(vector_a, a_vec._0[0]) + at(vector_a, __rust_mir_68._0[0])) by { simp() using { a_vec._0[0] == at(vector_a, a_vec._0[0]) + at(vector_a, __rust_mir_68._0[0]); } }
   have adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), __rust_mir_62_remaining)) == adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), at(lane_head, __rust_mir_62_remaining) - 4)) by { simp() using { __rust_mir_62_remaining == at(lane_head, __rust_mir_62_remaining) - 4; } }
   have to_integer(a_vec._0[0]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), __rust_mir_62_remaining)) by { arithmetic() using { to_integer(a_vec._0[0]) == to_integer(at(vector_a, a_vec._0[0]) + at(vector_a, __rust_mir_68._0[0])); adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), __rust_mir_62_remaining)) == adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), at(lane_head, __rust_mir_62_remaining) - 4)); to_integer(at(vector_a, a_vec._0[0]) + at(vector_a, __rust_mir_68._0[0])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), at(lane_head, __rust_mir_62_remaining) - 4)); } }
   have to_integer(b_vec._0[0]) == to_integer(at(vector_a, b_vec._0[0]) + (at(vector_a, a_vec._0[0]) + at(vector_a, __rust_mir_68._0[0]))) by { simp() using { b_vec._0[0] == at(vector_a, b_vec._0[0]) + (at(vector_a, a_vec._0[0]) + at(vector_a, __rust_mir_68._0[0])); } }
   have adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), __rust_mir_62_remaining)) == adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), at(lane_head, __rust_mir_62_remaining) - 4)) by { simp() using { __rust_mir_62_remaining == at(lane_head, __rust_mir_62_remaining) - 4; } }
   have to_integer(b_vec._0[0]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), __rust_mir_62_remaining)) by { arithmetic() using { to_integer(b_vec._0[0]) == to_integer(at(vector_a, b_vec._0[0]) + (at(vector_a, a_vec._0[0]) + at(vector_a, __rust_mir_68._0[0]))); adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), __rust_mir_62_remaining)) == adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), at(lane_head, __rust_mir_62_remaining) - 4)); to_integer(at(vector_a, b_vec._0[0]) + (at(vector_a, a_vec._0[0]) + at(vector_a, __rust_mir_68._0[0]))) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), at(lane_head, __rust_mir_62_remaining) - 4)); } }
   have a_vec._0[1] == at(vector_a, a_vec._0[1]) + at(vector_a, __rust_mir_68._0[1]) by { simp(); }
   have b_vec._0[1] == at(vector_a, b_vec._0[1]) + (at(vector_a, a_vec._0[1]) + at(vector_a, __rust_mir_68._0[1])) by { simp(); }
   have to_integer(a_vec._0[1]) == to_integer(at(vector_a, a_vec._0[1]) + at(vector_a, __rust_mir_68._0[1])) by { simp() using { a_vec._0[1] == at(vector_a, a_vec._0[1]) + at(vector_a, __rust_mir_68._0[1]); } }
   have adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), __rust_mir_62_remaining)) == adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), at(lane_head, __rust_mir_62_remaining) - 4)) by { simp() using { __rust_mir_62_remaining == at(lane_head, __rust_mir_62_remaining) - 4; } }
   have to_integer(a_vec._0[1]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), __rust_mir_62_remaining)) by { arithmetic() using { to_integer(a_vec._0[1]) == to_integer(at(vector_a, a_vec._0[1]) + at(vector_a, __rust_mir_68._0[1])); adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), __rust_mir_62_remaining)) == adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), at(lane_head, __rust_mir_62_remaining) - 4)); to_integer(at(vector_a, a_vec._0[1]) + at(vector_a, __rust_mir_68._0[1])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), at(lane_head, __rust_mir_62_remaining) - 4)); } }
   have to_integer(b_vec._0[1]) == to_integer(at(vector_a, b_vec._0[1]) + (at(vector_a, a_vec._0[1]) + at(vector_a, __rust_mir_68._0[1]))) by { simp() using { b_vec._0[1] == at(vector_a, b_vec._0[1]) + (at(vector_a, a_vec._0[1]) + at(vector_a, __rust_mir_68._0[1])); } }
   have adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), __rust_mir_62_remaining)) == adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), at(lane_head, __rust_mir_62_remaining) - 4)) by { simp() using { __rust_mir_62_remaining == at(lane_head, __rust_mir_62_remaining) - 4; } }
   have to_integer(b_vec._0[1]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), __rust_mir_62_remaining)) by { arithmetic() using { to_integer(b_vec._0[1]) == to_integer(at(vector_a, b_vec._0[1]) + (at(vector_a, a_vec._0[1]) + at(vector_a, __rust_mir_68._0[1]))); adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), __rust_mir_62_remaining)) == adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), at(lane_head, __rust_mir_62_remaining) - 4)); to_integer(at(vector_a, b_vec._0[1]) + (at(vector_a, a_vec._0[1]) + at(vector_a, __rust_mir_68._0[1]))) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), at(lane_head, __rust_mir_62_remaining) - 4)); } }
   have a_vec._0[2] == at(vector_a, a_vec._0[2]) + at(vector_a, __rust_mir_68._0[2]) by { simp(); }
   have b_vec._0[2] == at(vector_a, b_vec._0[2]) + (at(vector_a, a_vec._0[2]) + at(vector_a, __rust_mir_68._0[2])) by { simp(); }
   have to_integer(a_vec._0[2]) == to_integer(at(vector_a, a_vec._0[2]) + at(vector_a, __rust_mir_68._0[2])) by { simp() using { a_vec._0[2] == at(vector_a, a_vec._0[2]) + at(vector_a, __rust_mir_68._0[2]); } }
   have adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), __rust_mir_62_remaining)) == adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), at(lane_head, __rust_mir_62_remaining) - 4)) by { simp() using { __rust_mir_62_remaining == at(lane_head, __rust_mir_62_remaining) - 4; } }
   have to_integer(a_vec._0[2]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), __rust_mir_62_remaining)) by { arithmetic() using { to_integer(a_vec._0[2]) == to_integer(at(vector_a, a_vec._0[2]) + at(vector_a, __rust_mir_68._0[2])); adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), __rust_mir_62_remaining)) == adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), at(lane_head, __rust_mir_62_remaining) - 4)); to_integer(at(vector_a, a_vec._0[2]) + at(vector_a, __rust_mir_68._0[2])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), at(lane_head, __rust_mir_62_remaining) - 4)); } }
   have to_integer(b_vec._0[2]) == to_integer(at(vector_a, b_vec._0[2]) + (at(vector_a, a_vec._0[2]) + at(vector_a, __rust_mir_68._0[2]))) by { simp() using { b_vec._0[2] == at(vector_a, b_vec._0[2]) + (at(vector_a, a_vec._0[2]) + at(vector_a, __rust_mir_68._0[2])); } }
   have adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), __rust_mir_62_remaining)) == adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), at(lane_head, __rust_mir_62_remaining) - 4)) by { simp() using { __rust_mir_62_remaining == at(lane_head, __rust_mir_62_remaining) - 4; } }
   have to_integer(b_vec._0[2]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), __rust_mir_62_remaining)) by { arithmetic() using { to_integer(b_vec._0[2]) == to_integer(at(vector_a, b_vec._0[2]) + (at(vector_a, a_vec._0[2]) + at(vector_a, __rust_mir_68._0[2]))); adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), __rust_mir_62_remaining)) == adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), at(lane_head, __rust_mir_62_remaining) - 4)); to_integer(at(vector_a, b_vec._0[2]) + (at(vector_a, a_vec._0[2]) + at(vector_a, __rust_mir_68._0[2]))) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), at(lane_head, __rust_mir_62_remaining) - 4)); } }
   have a_vec._0[3] == at(vector_a, a_vec._0[3]) + at(vector_a, __rust_mir_68._0[3]) by { simp(); }
   have b_vec._0[3] == at(vector_a, b_vec._0[3]) + (at(vector_a, a_vec._0[3]) + at(vector_a, __rust_mir_68._0[3])) by { simp(); }
   have to_integer(a_vec._0[3]) == to_integer(at(vector_a, a_vec._0[3]) + at(vector_a, __rust_mir_68._0[3])) by { simp() using { a_vec._0[3] == at(vector_a, a_vec._0[3]) + at(vector_a, __rust_mir_68._0[3]); } }
   have adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), __rust_mir_62_remaining)) == adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), at(lane_head, __rust_mir_62_remaining) - 4)) by { simp() using { __rust_mir_62_remaining == at(lane_head, __rust_mir_62_remaining) - 4; } }
   have to_integer(a_vec._0[3]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), __rust_mir_62_remaining)) by { arithmetic() using { to_integer(a_vec._0[3]) == to_integer(at(vector_a, a_vec._0[3]) + at(vector_a, __rust_mir_68._0[3])); adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), __rust_mir_62_remaining)) == adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), at(lane_head, __rust_mir_62_remaining) - 4)); to_integer(at(vector_a, a_vec._0[3]) + at(vector_a, __rust_mir_68._0[3])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), at(lane_head, __rust_mir_62_remaining) - 4)); } }
   have to_integer(b_vec._0[3]) == to_integer(at(vector_a, b_vec._0[3]) + (at(vector_a, a_vec._0[3]) + at(vector_a, __rust_mir_68._0[3]))) by { simp() using { b_vec._0[3] == at(vector_a, b_vec._0[3]) + (at(vector_a, a_vec._0[3]) + at(vector_a, __rust_mir_68._0[3])); } }
   have adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), __rust_mir_62_remaining)) == adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), at(lane_head, __rust_mir_62_remaining) - 4)) by { simp() using { __rust_mir_62_remaining == at(lane_head, __rust_mir_62_remaining) - 4; } }
   have to_integer(b_vec._0[3]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), __rust_mir_62_remaining)) by { arithmetic() using { to_integer(b_vec._0[3]) == to_integer(at(vector_a, b_vec._0[3]) + (at(vector_a, a_vec._0[3]) + at(vector_a, __rust_mir_68._0[3]))); adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), __rust_mir_62_remaining)) == adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), at(lane_head, __rust_mir_62_remaining) - 4)); to_integer(at(vector_a, b_vec._0[3]) + (at(vector_a, a_vec._0[3]) + at(vector_a, __rust_mir_68._0[3]))) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((int32)(uint32)bytes_len), at(lane_head, __rust_mir_62_remaining) - 4)); } }
   have 0 <= __rust_mir_62_remaining by { arithmetic() using { __rust_mir_62_remaining == at(lane_head, __rust_mir_62_remaining) - 4; 4 <= at(lane_head, __rust_mir_62_remaining); } }
   have __rust_mir_62_remaining <= old((int32)(uint32)bytes_len) by { arithmetic() using { __rust_mir_62_remaining == at(lane_head, __rust_mir_62_remaining) - 4; 4 <= at(lane_head, __rust_mir_62_remaining); at(lane_head, __rust_mir_62_remaining) <= old((int32)(uint32)bytes_len); old((int32)(uint32)bytes_len) <= 22204; } }
   have 0 <= __rust_mir_62_remaining and __rust_mir_62_remaining <= old((int32)(uint32)bytes_len) by { assumption(); }
   have __rust_mir_62_remaining % 4 == 0 by { rewrite(__rust_mir_62_remaining == at(lane_head, __rust_mir_62_remaining) - 4); normalize() using { at(lane_head, __rust_mir_62_remaining) % 4 == 0; 4 <= at(lane_head, __rust_mir_62_remaining); at(lane_head, __rust_mir_62_remaining) <= old((int32)(uint32)bytes_len); old((int32)(uint32)bytes_len) <= 22204; } }
   have __rust_mir_62_cursor == at(lane_head, __rust_mir_62_cursor) + 4 by { simp(); }
   have (old((int32)(uint32)bytes_len) - at(lane_head, __rust_mir_62_remaining)) + 4 == old((int32)(uint32)bytes_len) - __rust_mir_62_remaining by { arithmetic() using { __rust_mir_62_remaining == at(lane_head, __rust_mir_62_remaining) - 4; 4 <= at(lane_head, __rust_mir_62_remaining); at(lane_head, __rust_mir_62_remaining) <= old((int32)(uint32)bytes_len); old((int32)(uint32)bytes_len) <= 22204; } }
   have 0 <= old((int32)(uint32)bytes_len) - at(lane_head, __rust_mir_62_remaining) by { arithmetic() using { 4 <= at(lane_head, __rust_mir_62_remaining); at(lane_head, __rust_mir_62_remaining) <= old((int32)(uint32)bytes_len); old((int32)(uint32)bytes_len) <= 22204; } }
   have old((int32)(uint32)bytes_len) - at(lane_head, __rust_mir_62_remaining) <= 22200 by { arithmetic() using { 4 <= at(lane_head, __rust_mir_62_remaining); at(lane_head, __rust_mir_62_remaining) <= old((int32)(uint32)bytes_len); old((int32)(uint32)bytes_len) <= 22204; } }
   have 0 <= at(lane_head, __rust_mir_62_remaining) by { arithmetic() using { 4 <= at(lane_head, __rust_mir_62_remaining); } }
   have defined(old((int32)(uint32)bytes_len) - at(lane_head, __rust_mir_62_remaining)) by { apply(int32_nonnegative_subtract_within_value_is_defined(old((int32)(uint32)bytes_len), at(lane_head, __rust_mir_62_remaining))) using { 0 <= at(lane_head, __rust_mir_62_remaining); at(lane_head, __rust_mir_62_remaining) <= old((int32)(uint32)bytes_len); } }
   have (old(bytes) + (old((int32)(uint32)bytes_len) - at(lane_head, __rust_mir_62_remaining))) + 4 == old(bytes) + ((old((int32)(uint32)bytes_len) - at(lane_head, __rust_mir_62_remaining)) + 4) by { apply(adler_bounded_pointer_association(old(bytes), old((int32)(uint32)bytes_len) - at(lane_head, __rust_mir_62_remaining))) using { defined(old((int32)(uint32)bytes_len) - at(lane_head, __rust_mir_62_remaining)); 0 <= old((int32)(uint32)bytes_len) - at(lane_head, __rust_mir_62_remaining); old((int32)(uint32)bytes_len) - at(lane_head, __rust_mir_62_remaining) <= 22200; } }
   have __rust_mir_62_cursor == old(bytes) + (old((int32)(uint32)bytes_len) - __rust_mir_62_remaining) by { rewrite(__rust_mir_62_cursor == at(lane_head, __rust_mir_62_cursor) + 4); rewrite(at(lane_head, __rust_mir_62_cursor) == old(bytes) + (old((int32)(uint32)bytes_len) - at(lane_head, __rust_mir_62_remaining))); rewrite((old(bytes) + (old((int32)(uint32)bytes_len) - at(lane_head, __rust_mir_62_remaining))) + 4 == old(bytes) + ((old((int32)(uint32)bytes_len) - at(lane_head, __rust_mir_62_remaining)) + 4)); rewrite((old((int32)(uint32)bytes_len) - at(lane_head, __rust_mir_62_remaining)) + 4 == old((int32)(uint32)bytes_len) - __rust_mir_62_remaining); normalize() using {}; }
   have __rust_mir_62_remaining < at(lane_head, __rust_mir_62_remaining) by { arithmetic() using { __rust_mir_62_remaining == at(lane_head, __rust_mir_62_remaining) - 4; 4 <= at(lane_head, __rust_mir_62_remaining); at(lane_head, __rust_mir_62_remaining) <= old((int32)(uint32)bytes_len); old((int32)(uint32)bytes_len) <= 22204; } }
   have viewable(bytes[0..(int32)(uint32)bytes_len]) by { transport(at(lane_head, viewable(bytes[0..(int32)(uint32)bytes_len])), viewable(bytes[0..(int32)(uint32)bytes_len])) using { at(lane_head, viewable(bytes[0..(int32)(uint32)bytes_len])); bytes == old(bytes); bytes_len == old(bytes_len); 0 <= old((int32)(uint32)bytes_len); old((int32)(uint32)bytes_len) <= 22204; } }
   close_invariants by {
    both {
     normalize();
    } and {
     both {
      intro();
      normalize();
     } and {
      both {
       intro();
       intro();
       assumption();
      } and {
       both {
        intro();
        intro();
        intro();
        assumption();
       } and {
        both {
         intro();
         intro();
         intro();
         intro();
         assumption();
        } and {
         both {
          intro();
          intro();
          intro();
          intro();
          intro();
          assumption();
         } and {
          both {
           intro();
           intro();
           intro();
           intro();
           intro();
           intro();
           assumption();
          } and {
           both {
            intro();
            intro();
            intro();
            intro();
            intro();
            intro();
            intro();
            normalize();
           } and {
            both {
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             assumption();
            } and {
             both {
              intro();
              intro();
              intro();
              intro();
              intro();
              intro();
              intro();
              intro();
              intro();
              assumption();
             } and {
              both {
               intro();
               intro();
               intro();
               intro();
               intro();
               intro();
               intro();
               intro();
               intro();
               intro();
               intro();
               assumption();
              } and {
               both {
                intro();
                intro();
                intro();
                intro();
                intro();
                intro();
                intro();
                intro();
                intro();
                intro();
                intro();
                intro();
                assumption();
               } and {
                both {
                 intro();
                 intro();
                 intro();
                 intro();
                 intro();
                 intro();
                 intro();
                 intro();
                 intro();
                 intro();
                 intro();
                 intro();
                 intro();
                 assumption();
                } and {
                 both {
                  intro();
                  intro();
                  intro();
                  intro();
                  intro();
                  intro();
                  intro();
                  intro();
                  intro();
                  intro();
                  intro();
                  intro();
                  intro();
                  intro();
                  assumption();
                 } and {
                  both {
                   intro();
                   intro();
                   intro();
                   intro();
                   intro();
                   intro();
                   intro();
                   intro();
                   intro();
                   intro();
                   intro();
                   intro();
                   intro();
                   intro();
                   intro();
                   assumption();
                  } and {
                   both {
                    intro();
                    intro();
                    intro();
                    intro();
                    intro();
                    intro();
                    intro();
                    intro();
                    intro();
                    intro();
                    intro();
                    intro();
                    intro();
                    intro();
                    intro();
                    intro();
                    assumption();
                   } and {
                    both {
                     intro();
                     intro();
                     intro();
                     intro();
                     intro();
                     intro();
                     intro();
                     intro();
                     intro();
                     intro();
                     intro();
                     intro();
                     intro();
                     intro();
                     intro();
                     intro();
                     intro();
                     assumption();
                    } and {
                     both {
                      intro();
                      intro();
                      intro();
                      intro();
                      intro();
                      intro();
                      intro();
                      intro();
                      intro();
                      intro();
                      intro();
                      intro();
                      intro();
                      intro();
                      intro();
                      intro();
                      intro();
                      intro();
                      assumption();
                     } and {
                      both {
                       intro();
                       intro();
                       intro();
                       intro();
                       intro();
                       intro();
                       intro();
                       intro();
                       intro();
                       intro();
                       intro();
                       intro();
                       intro();
                       intro();
                       intro();
                       intro();
                       intro();
                       intro();
                       intro();
                       assumption();
                      } and {
                       both {
                        assumption();
                       } and {
                        assumption();
                       }
                      }
                     }
                    }
                   }
                  }
                 }
                }
               }
              }
             }
            }
           }
          }
         }
        }
       }
      }
     }
    }
   }
  }
 }
 have __rust_mir_62_remaining < 4 by { cases { not (0 < __rust_mir_62_remaining) => { have __rust_mir_62_remaining <= 0 by { simp(); } arithmetic() using { __rust_mir_62_remaining <= 0; } } not (4 <= __rust_mir_62_remaining) => { simp(); } } }
 have __rust_mir_62_remaining % 4 == __rust_mir_62_remaining by { normalize() using { 0 <= __rust_mir_62_remaining; __rust_mir_62_remaining < 4; } }
 have __rust_mir_62_remaining == 0 by { simp() using { __rust_mir_62_remaining % 4 == 0; __rust_mir_62_remaining % 4 == __rust_mir_62_remaining; } }
 have remainder_len == bytes_len - (bytes_len - bytes_len % 4u64) by { simp() using {}; }
 have remainder_len == 0u64 by { rewrite(remainder_len == bytes_len - (bytes_len - bytes_len % 4u64)); rewrite(bytes_len % 4u64 == 0u64); normalize(); }
 execute_until(assignment(__rust_mir_80, 0)); step();
 have __rust_mir_77 == (uint32)remainder_chunk_len by { simp(); }
 have remainder_chunk_len == bytes_len by { assumption(); }
 apply(adler_small_length_cast(bytes_len)) using { bytes_len <= 22204u64; }
 have __rust_mir_77 <= 22204u32 by { rewrite(__rust_mir_77 == (uint32)remainder_chunk_len); rewrite(remainder_chunk_len == bytes_len); assumption(); }
 have __rust_mir_80 <= 65520u32 by { simp() using { a <= 65520u32; } }
 apply(adler_scalar_batch_product_bound(__rust_mir_77, __rust_mir_80)) using { __rust_mir_77 <= 22204u32; __rust_mir_80 <= 65520u32; }
 have to_integer(__rust_mir_77) * to_integer(__rust_mir_80) <= 4294967295 by { arithmetic() using { to_integer(__rust_mir_77) * to_integer(__rust_mir_80) <= 1454806080; } }
 apply(uint32_mul_guard_by_integer_bound(__rust_mir_77, __rust_mir_80)) using { to_integer(__rust_mir_77) * to_integer(__rust_mir_80) <= 4294967295; }
 mark seed_product;
 have to_integer(at(seed_product, __rust_mir_77)) * to_integer(at(seed_product, __rust_mir_80)) <= 1454806080 by { simp() using { to_integer(__rust_mir_77) * to_integer(__rust_mir_80) <= 1454806080; } }
 have at(seed_product, __rust_mir_80) == 0u32 or at(seed_product, __rust_mir_77) <= 4294967295u32 / at(seed_product, __rust_mir_80) by { simp() using { __rust_mir_80 == 0u32 or __rust_mir_77 <= 4294967295u32 / __rust_mir_80; } }
 apply(uint32_mul_to_integer(at(seed_product, __rust_mir_77), at(seed_product, __rust_mir_80))) using { at(seed_product, __rust_mir_80) == 0u32 or at(seed_product, __rust_mir_77) <= 4294967295u32 / at(seed_product, __rust_mir_80); }
 if __rust_mir_80 == 0u32 {
  execute_until(assignment(__rust_mir_76, 0)); step();
 } else {
  have __rust_mir_77 <= 4294967295u32 / __rust_mir_80 by {
   cases {
    __rust_mir_80 == 0u32 => { contradiction(not (__rust_mir_80 == 0u32)); }
    __rust_mir_77 <= 4294967295u32 / __rust_mir_80 => { assumption(); }
   }
  }
  execute_until(assignment(__rust_mir_76, 0)); step();
 }
 have __rust_mir_76 == at(seed_product, __rust_mir_77) * at(seed_product, __rust_mir_80) by { simp(); }
 have to_integer(__rust_mir_76) <= 1454806080 by { rewrite(__rust_mir_76 == at(seed_product, __rust_mir_77) * at(seed_product, __rust_mir_80)); rewrite(to_integer(at(seed_product, __rust_mir_77) * at(seed_product, __rust_mir_80)) == to_integer(at(seed_product, __rust_mir_77)) * to_integer(at(seed_product, __rust_mir_80))); assumption(); }
 have b <= 65520u32 by { assumption(); }
 apply(uint32_less_equal_to_integer(b, 65520u32)) using { b <= 65520u32; }
 have to_integer(b) + to_integer(__rust_mir_76) <= 4294967295 by { arithmetic() using { to_integer(b) <= 65520; to_integer(__rust_mir_76) <= 1454806080; } }
 apply(uint32_widened_add_guard_by_integer_bound(b, __rust_mir_76)) using { to_integer(b) + to_integer(__rust_mir_76) <= 4294967295; }
 execute_until(assignment(__rust_mir_88, 0));
 have __rust_checked_82 == 65521u32 by { simp(); }
 have 65521u32 == __rust_checked_82 by { simp() using { __rust_checked_82 == 65521u32; } }
 have b_vec._0[0] < __rust_checked_82 by { simp(); }
 have b_vec._0[0] < 65521u32 by { rewrite(65521u32 == __rust_checked_82); assumption(); }
 have b_vec._0[0] <= 4294967295u32 / 4u32 by { arithmetic() using { b_vec._0[0] < 65521u32; } }
 have b_vec._0[1] < __rust_checked_82 by { simp(); }
 have b_vec._0[1] < 65521u32 by { rewrite(65521u32 == __rust_checked_82); assumption(); }
 have b_vec._0[1] <= 4294967295u32 / 4u32 by { arithmetic() using { b_vec._0[1] < 65521u32; } }
 have b_vec._0[2] < __rust_checked_82 by { simp(); }
 have b_vec._0[2] < 65521u32 by { rewrite(65521u32 == __rust_checked_82); assumption(); }
 have b_vec._0[2] <= 4294967295u32 / 4u32 by { arithmetic() using { b_vec._0[2] < 65521u32; } }
 have b_vec._0[3] < __rust_checked_82 by { simp(); }
 have b_vec._0[3] < 65521u32 by { rewrite(65521u32 == __rust_checked_82); assumption(); }
 have b_vec._0[3] <= 4294967295u32 / 4u32 by { arithmetic() using { b_vec._0[3] < 65521u32; } }
 apply(uint32_less_than_to_integer(b_vec._0[0], 65521u32)) using { b_vec._0[0] < 65521u32; }
 have to_integer(b_vec._0[0]) <= 65520 by { arithmetic() using { to_integer(b_vec._0[0]) < 65521; } }
 apply(uint32_less_than_to_integer(b_vec._0[1], 65521u32)) using { b_vec._0[1] < 65521u32; }
 have to_integer(b_vec._0[1]) <= 65520 by { arithmetic() using { to_integer(b_vec._0[1]) < 65521; } }
 apply(uint32_less_than_to_integer(b_vec._0[2], 65521u32)) using { b_vec._0[2] < 65521u32; }
 have to_integer(b_vec._0[2]) <= 65520 by { arithmetic() using { to_integer(b_vec._0[2]) < 65521; } }
 apply(uint32_less_than_to_integer(b_vec._0[3], 65521u32)) using { b_vec._0[3] < 65521u32; }
 have to_integer(b_vec._0[3]) <= 65520 by { arithmetic() using { to_integer(b_vec._0[3]) < 65521; } }
 mark weighted_b;
 execute_until(assignment(__rust_mir_91, 0));
 have __rust_checked_85 == 65521u32 by { simp(); }
 have 65521u32 == __rust_checked_85 by { simp() using { __rust_checked_85 == 65521u32; } }
 have a_vec._0[0] < __rust_checked_85 by { simp(); }
 have a_vec._0[0] < 65521u32 by { rewrite(65521u32 == __rust_checked_85); assumption(); }
 have a_vec._0[1] < __rust_checked_85 by { simp(); }
 have a_vec._0[1] < 65521u32 by { rewrite(65521u32 == __rust_checked_85); assumption(); }
 have a_vec._0[2] < __rust_checked_85 by { simp(); }
 have a_vec._0[2] < 65521u32 by { rewrite(65521u32 == __rust_checked_85); assumption(); }
 have a_vec._0[3] < __rust_checked_85 by { simp(); }
 have a_vec._0[3] < 65521u32 by { rewrite(65521u32 == __rust_checked_85); assumption(); }
 have to_integer(b_vec._0[0]) == to_integer(at(weighted_b, b_vec._0[0])) * 4 by { simp(); }
 have to_integer(at(weighted_b, b_vec._0[0])) <= 65520 by { simp(); }
 have to_integer(b_vec._0[0]) <= 262080 by { arithmetic() using { to_integer(b_vec._0[0]) == to_integer(at(weighted_b, b_vec._0[0])) * 4; to_integer(at(weighted_b, b_vec._0[0])) <= 65520; } }
 have to_integer(b_vec._0[1]) == to_integer(at(weighted_b, b_vec._0[1])) * 4 by { simp(); }
 have to_integer(at(weighted_b, b_vec._0[1])) <= 65520 by { simp(); }
 have to_integer(b_vec._0[1]) <= 262080 by { arithmetic() using { to_integer(b_vec._0[1]) == to_integer(at(weighted_b, b_vec._0[1])) * 4; to_integer(at(weighted_b, b_vec._0[1])) <= 65520; } }
 have to_integer(b_vec._0[2]) == to_integer(at(weighted_b, b_vec._0[2])) * 4 by { simp(); }
 have to_integer(at(weighted_b, b_vec._0[2])) <= 65520 by { simp(); }
 have to_integer(b_vec._0[2]) <= 262080 by { arithmetic() using { to_integer(b_vec._0[2]) == to_integer(at(weighted_b, b_vec._0[2])) * 4; to_integer(at(weighted_b, b_vec._0[2])) <= 65520; } }
 have to_integer(b_vec._0[3]) == to_integer(at(weighted_b, b_vec._0[3])) * 4 by { simp(); }
 have to_integer(at(weighted_b, b_vec._0[3])) <= 65520 by { simp(); }
 have to_integer(b_vec._0[3]) <= 262080 by { arithmetic() using { to_integer(b_vec._0[3]) == to_integer(at(weighted_b, b_vec._0[3])) * 4; to_integer(at(weighted_b, b_vec._0[3])) <= 65520; } }
 apply(adler_recombine_lane_1(a_vec._0[1], b_vec._0[1])) using { a_vec._0[1] < 65521u32; to_integer(b_vec._0[1]) <= 262080; }
 apply(adler_recombine_lane_2(a_vec._0[2], b_vec._0[2])) using { a_vec._0[2] < 65521u32; to_integer(b_vec._0[2]) <= 262080; }
 apply(adler_recombine_lane_3(a_vec._0[3], b_vec._0[3])) using { a_vec._0[3] < 65521u32; to_integer(b_vec._0[3]) <= 262080; }
 apply(adler_recombine_difference(a_vec._0[2])) using { a_vec._0[2] < 65521u32; }
 have 65521u32 - a_vec._0[2] <= 4294967295u32 / 2u32 by { arithmetic() using { 65521u32 - a_vec._0[2] <= 65521u32; } }
 apply(adler_recombine_difference(a_vec._0[3])) using { a_vec._0[3] < 65521u32; }
 have 65521u32 - a_vec._0[3] <= 4294967295u32 / 3u32 by { arithmetic() using { 65521u32 - a_vec._0[3] <= 65521u32; } }
 execute_until(loop(3));
 have a <= 65520u32 by { assumption(); }
 apply(uint32_less_equal_to_integer(a, 65520u32)) using { a <= 65520u32; }
 execute_until(assignment(__rust_mir_121, 0));
 have av == a_vec._0[0] by { simp(); }
 apply(uint32_less_than_to_integer(a_vec._0[0], 65521u32)) using { a_vec._0[0] < 65521u32; }
 have to_integer(av) <= 65520 by { rewrite(av == a_vec._0[0]); arithmetic() using { to_integer(a_vec._0[0]) < 65521; } }
 step();
 have to_integer(__rust_mir_121) <= 65520 by { simp() using { to_integer(av) <= 65520; } }
 have to_integer(a) + to_integer(__rust_mir_121) <= 4294967295 by { arithmetic() using { to_integer(a) <= 65520; to_integer(__rust_mir_121) <= 65520; } }
 apply(uint32_widened_add_guard_by_integer_bound(a, __rust_mir_121)) using { to_integer(a) + to_integer(__rust_mir_121) <= 4294967295; }
 execute_until(assignment(__rust_mir_122, 0));
 mark small_sum_a_0;
 have to_integer(at(small_sum_a_0, a)) <= 65520 by { simp() using { to_integer(a) <= 65520; } }
 have to_integer(at(small_sum_a_0, __rust_mir_121)) <= 65520 by { simp() using { to_integer(__rust_mir_121) <= 65520; } }
 have to_integer(at(small_sum_a_0, a)) + to_integer(at(small_sum_a_0, __rust_mir_121)) <= 4294967295 by { arithmetic() using { to_integer(at(small_sum_a_0, a)) <= 65520; to_integer(at(small_sum_a_0, __rust_mir_121)) <= 65520; } }
 step();
 have __rust_mir_122 == at(small_sum_a_0, a) + at(small_sum_a_0, __rust_mir_121) by { simp(); }
 apply(uint32_add_to_integer(at(small_sum_a_0, a), at(small_sum_a_0, __rust_mir_121))) using { to_integer(at(small_sum_a_0, a)) + to_integer(at(small_sum_a_0, __rust_mir_121)) <= 4294967295; }
 have to_integer(__rust_mir_122) <= 131040 by { rewrite(__rust_mir_122 == at(small_sum_a_0, a) + at(small_sum_a_0, __rust_mir_121)); rewrite(to_integer(at(small_sum_a_0, a) + at(small_sum_a_0, __rust_mir_121)) == to_integer(at(small_sum_a_0, a)) + to_integer(at(small_sum_a_0, __rust_mir_121))); arithmetic() using { to_integer(at(small_sum_a_0, a)) <= 65520; to_integer(at(small_sum_a_0, __rust_mir_121)) <= 65520; } }
 execute_until(assignment(a, 1)); step();
 have to_integer(a) <= 131040 by { simp() using { to_integer(__rust_mir_122) <= 131040; } }
 step(); step(); step(); step(); step(); step(); step(); step();
 execute_until(assignment(__rust_mir_121, 0));
 have av == a_vec._0[1] by { simp(); }
 apply(uint32_less_than_to_integer(a_vec._0[1], 65521u32)) using { a_vec._0[1] < 65521u32; }
 have to_integer(av) <= 65520 by { rewrite(av == a_vec._0[1]); arithmetic() using { to_integer(a_vec._0[1]) < 65521; } }
 step();
 have to_integer(__rust_mir_121) <= 65520 by { simp() using { to_integer(av) <= 65520; } }
 have to_integer(a) + to_integer(__rust_mir_121) <= 4294967295 by { arithmetic() using { to_integer(a) <= 131040; to_integer(__rust_mir_121) <= 65520; } }
 apply(uint32_widened_add_guard_by_integer_bound(a, __rust_mir_121)) using { to_integer(a) + to_integer(__rust_mir_121) <= 4294967295; }
 execute_until(assignment(__rust_mir_122, 0));
 mark small_sum_a_1;
 have to_integer(at(small_sum_a_1, a)) <= 131040 by { simp() using { to_integer(a) <= 131040; } }
 have to_integer(at(small_sum_a_1, __rust_mir_121)) <= 65520 by { simp() using { to_integer(__rust_mir_121) <= 65520; } }
 have to_integer(at(small_sum_a_1, a)) + to_integer(at(small_sum_a_1, __rust_mir_121)) <= 4294967295 by { arithmetic() using { to_integer(at(small_sum_a_1, a)) <= 131040; to_integer(at(small_sum_a_1, __rust_mir_121)) <= 65520; } }
 step();
 have __rust_mir_122 == at(small_sum_a_1, a) + at(small_sum_a_1, __rust_mir_121) by { simp(); }
 apply(uint32_add_to_integer(at(small_sum_a_1, a), at(small_sum_a_1, __rust_mir_121))) using { to_integer(at(small_sum_a_1, a)) + to_integer(at(small_sum_a_1, __rust_mir_121)) <= 4294967295; }
 have to_integer(__rust_mir_122) <= 196560 by { rewrite(__rust_mir_122 == at(small_sum_a_1, a) + at(small_sum_a_1, __rust_mir_121)); rewrite(to_integer(at(small_sum_a_1, a) + at(small_sum_a_1, __rust_mir_121)) == to_integer(at(small_sum_a_1, a)) + to_integer(at(small_sum_a_1, __rust_mir_121))); arithmetic() using { to_integer(at(small_sum_a_1, a)) <= 131040; to_integer(at(small_sum_a_1, __rust_mir_121)) <= 65520; } }
 execute_until(assignment(a, 1)); step();
 have to_integer(a) <= 196560 by { simp() using { to_integer(__rust_mir_122) <= 196560; } }
 step(); step(); step(); step(); step(); step(); step(); step();
 execute_until(assignment(__rust_mir_121, 0));
 have av == a_vec._0[2] by { simp(); }
 apply(uint32_less_than_to_integer(a_vec._0[2], 65521u32)) using { a_vec._0[2] < 65521u32; }
 have to_integer(av) <= 65520 by { rewrite(av == a_vec._0[2]); arithmetic() using { to_integer(a_vec._0[2]) < 65521; } }
 step();
 have to_integer(__rust_mir_121) <= 65520 by { simp() using { to_integer(av) <= 65520; } }
 have to_integer(a) + to_integer(__rust_mir_121) <= 4294967295 by { arithmetic() using { to_integer(a) <= 196560; to_integer(__rust_mir_121) <= 65520; } }
 apply(uint32_widened_add_guard_by_integer_bound(a, __rust_mir_121)) using { to_integer(a) + to_integer(__rust_mir_121) <= 4294967295; }
 execute_until(assignment(__rust_mir_122, 0));
 mark small_sum_a_2;
 have to_integer(at(small_sum_a_2, a)) <= 196560 by { simp() using { to_integer(a) <= 196560; } }
 have to_integer(at(small_sum_a_2, __rust_mir_121)) <= 65520 by { simp() using { to_integer(__rust_mir_121) <= 65520; } }
 have to_integer(at(small_sum_a_2, a)) + to_integer(at(small_sum_a_2, __rust_mir_121)) <= 4294967295 by { arithmetic() using { to_integer(at(small_sum_a_2, a)) <= 196560; to_integer(at(small_sum_a_2, __rust_mir_121)) <= 65520; } }
 step();
 have __rust_mir_122 == at(small_sum_a_2, a) + at(small_sum_a_2, __rust_mir_121) by { simp(); }
 apply(uint32_add_to_integer(at(small_sum_a_2, a), at(small_sum_a_2, __rust_mir_121))) using { to_integer(at(small_sum_a_2, a)) + to_integer(at(small_sum_a_2, __rust_mir_121)) <= 4294967295; }
 have to_integer(__rust_mir_122) <= 262080 by { rewrite(__rust_mir_122 == at(small_sum_a_2, a) + at(small_sum_a_2, __rust_mir_121)); rewrite(to_integer(at(small_sum_a_2, a) + at(small_sum_a_2, __rust_mir_121)) == to_integer(at(small_sum_a_2, a)) + to_integer(at(small_sum_a_2, __rust_mir_121))); arithmetic() using { to_integer(at(small_sum_a_2, a)) <= 196560; to_integer(at(small_sum_a_2, __rust_mir_121)) <= 65520; } }
 execute_until(assignment(a, 1)); step();
 have to_integer(a) <= 262080 by { simp() using { to_integer(__rust_mir_122) <= 262080; } }
 step(); step(); step(); step(); step(); step(); step(); step();
 execute_until(assignment(__rust_mir_121, 0));
 have av == a_vec._0[3] by { simp(); }
 apply(uint32_less_than_to_integer(a_vec._0[3], 65521u32)) using { a_vec._0[3] < 65521u32; }
 have to_integer(av) <= 65520 by { rewrite(av == a_vec._0[3]); arithmetic() using { to_integer(a_vec._0[3]) < 65521; } }
 step();
 have to_integer(__rust_mir_121) <= 65520 by { simp() using { to_integer(av) <= 65520; } }
 have to_integer(a) + to_integer(__rust_mir_121) <= 4294967295 by { arithmetic() using { to_integer(a) <= 262080; to_integer(__rust_mir_121) <= 65520; } }
 apply(uint32_widened_add_guard_by_integer_bound(a, __rust_mir_121)) using { to_integer(a) + to_integer(__rust_mir_121) <= 4294967295; }
 execute_until(assignment(__rust_mir_122, 0));
 mark small_sum_a_3;
 have to_integer(at(small_sum_a_3, a)) <= 262080 by { simp() using { to_integer(a) <= 262080; } }
 have to_integer(at(small_sum_a_3, __rust_mir_121)) <= 65520 by { simp() using { to_integer(__rust_mir_121) <= 65520; } }
 have to_integer(at(small_sum_a_3, a)) + to_integer(at(small_sum_a_3, __rust_mir_121)) <= 4294967295 by { arithmetic() using { to_integer(at(small_sum_a_3, a)) <= 262080; to_integer(at(small_sum_a_3, __rust_mir_121)) <= 65520; } }
 step();
 have __rust_mir_122 == at(small_sum_a_3, a) + at(small_sum_a_3, __rust_mir_121) by { simp(); }
 apply(uint32_add_to_integer(at(small_sum_a_3, a), at(small_sum_a_3, __rust_mir_121))) using { to_integer(at(small_sum_a_3, a)) + to_integer(at(small_sum_a_3, __rust_mir_121)) <= 4294967295; }
 have to_integer(__rust_mir_122) <= 327600 by { rewrite(__rust_mir_122 == at(small_sum_a_3, a) + at(small_sum_a_3, __rust_mir_121)); rewrite(to_integer(at(small_sum_a_3, a) + at(small_sum_a_3, __rust_mir_121)) == to_integer(at(small_sum_a_3, a)) + to_integer(at(small_sum_a_3, __rust_mir_121))); arithmetic() using { to_integer(at(small_sum_a_3, a)) <= 262080; to_integer(at(small_sum_a_3, __rust_mir_121)) <= 65520; } }
 execute_until(assignment(a, 1)); step();
 have to_integer(a) <= 327600 by { simp() using { to_integer(__rust_mir_122) <= 327600; } }
 step(); step(); step(); step(); step(); step(); step(); step();
 execute_until(loop(4));
 have __rust_checked_79 == 65521u32 by { simp(); }
 have 65521u32 == __rust_checked_79 by { simp() using { __rust_checked_79 == 65521u32; } }
 have b == __rust_checked_77 % __rust_checked_79 by { simp(); }
 have __rust_checked_79 != 0u32 by { rewrite(__rust_checked_79 == 65521u32); normalize(); }
 apply(uint32_remainder_less_than_divisor(__rust_checked_77, __rust_checked_79)) using { __rust_checked_79 != 0u32; }
 have b < __rust_checked_79 by { rewrite(b == __rust_checked_77 % __rust_checked_79); assumption(); }
 have b < 65521u32 by { rewrite(65521u32 == __rust_checked_79); assumption(); }
 apply(uint32_less_than_to_integer(b, 65521u32)) using { b < 65521u32; }
 have to_integer(b) <= 65520 by { arithmetic() using { to_integer(b) < 65521; } }
 have to_integer(b_vec._0[0]) <= 262080 by { simp(); }
 execute_until(assignment(__rust_mir_133, 0));
 have bv == b_vec._0[0] by { simp(); }
 have to_integer(bv) <= 262080 by { rewrite(bv == b_vec._0[0]); assumption(); }
 step();
 have to_integer(__rust_mir_133) <= 262080 by { simp() using { to_integer(bv) <= 262080; } }
 have to_integer(b) + to_integer(__rust_mir_133) <= 4294967295 by { arithmetic() using { to_integer(b) <= 65520; to_integer(__rust_mir_133) <= 262080; } }
 apply(uint32_widened_add_guard_by_integer_bound(b, __rust_mir_133)) using { to_integer(b) + to_integer(__rust_mir_133) <= 4294967295; }
 execute_until(assignment(__rust_mir_134, 0));
 mark small_sum_b_0;
 have to_integer(at(small_sum_b_0, b)) <= 65520 by { simp() using { to_integer(b) <= 65520; } }
 have to_integer(at(small_sum_b_0, __rust_mir_133)) <= 262080 by { simp() using { to_integer(__rust_mir_133) <= 262080; } }
 have to_integer(at(small_sum_b_0, b)) + to_integer(at(small_sum_b_0, __rust_mir_133)) <= 4294967295 by { arithmetic() using { to_integer(at(small_sum_b_0, b)) <= 65520; to_integer(at(small_sum_b_0, __rust_mir_133)) <= 262080; } }
 step();
 have __rust_mir_134 == at(small_sum_b_0, b) + at(small_sum_b_0, __rust_mir_133) by { simp(); }
 apply(uint32_add_to_integer(at(small_sum_b_0, b), at(small_sum_b_0, __rust_mir_133))) using { to_integer(at(small_sum_b_0, b)) + to_integer(at(small_sum_b_0, __rust_mir_133)) <= 4294967295; }
 have to_integer(__rust_mir_134) <= 327600 by { rewrite(__rust_mir_134 == at(small_sum_b_0, b) + at(small_sum_b_0, __rust_mir_133)); rewrite(to_integer(at(small_sum_b_0, b) + at(small_sum_b_0, __rust_mir_133)) == to_integer(at(small_sum_b_0, b)) + to_integer(at(small_sum_b_0, __rust_mir_133))); arithmetic() using { to_integer(at(small_sum_b_0, b)) <= 65520; to_integer(at(small_sum_b_0, __rust_mir_133)) <= 262080; } }
 execute_until(assignment(b, 5)); step();
 have to_integer(b) <= 327600 by { simp() using { to_integer(__rust_mir_134) <= 327600; } }
 step(); step(); step(); step(); step(); step(); step(); step();
 have to_integer(b_vec._0[1]) <= 327601 by { simp(); }
 execute_until(assignment(__rust_mir_133, 0));
 have bv == b_vec._0[1] by { simp(); }
 have to_integer(bv) <= 327601 by { rewrite(bv == b_vec._0[1]); assumption(); }
 step();
 have to_integer(__rust_mir_133) <= 327601 by { simp() using { to_integer(bv) <= 327601; } }
 have to_integer(b) + to_integer(__rust_mir_133) <= 4294967295 by { arithmetic() using { to_integer(b) <= 327600; to_integer(__rust_mir_133) <= 327601; } }
 apply(uint32_widened_add_guard_by_integer_bound(b, __rust_mir_133)) using { to_integer(b) + to_integer(__rust_mir_133) <= 4294967295; }
 execute_until(assignment(__rust_mir_134, 0));
 mark small_sum_b_1;
 have to_integer(at(small_sum_b_1, b)) <= 327600 by { simp() using { to_integer(b) <= 327600; } }
 have to_integer(at(small_sum_b_1, __rust_mir_133)) <= 327601 by { simp() using { to_integer(__rust_mir_133) <= 327601; } }
 have to_integer(at(small_sum_b_1, b)) + to_integer(at(small_sum_b_1, __rust_mir_133)) <= 4294967295 by { arithmetic() using { to_integer(at(small_sum_b_1, b)) <= 327600; to_integer(at(small_sum_b_1, __rust_mir_133)) <= 327601; } }
 step();
 have __rust_mir_134 == at(small_sum_b_1, b) + at(small_sum_b_1, __rust_mir_133) by { simp(); }
 apply(uint32_add_to_integer(at(small_sum_b_1, b), at(small_sum_b_1, __rust_mir_133))) using { to_integer(at(small_sum_b_1, b)) + to_integer(at(small_sum_b_1, __rust_mir_133)) <= 4294967295; }
 have to_integer(__rust_mir_134) <= 655201 by { rewrite(__rust_mir_134 == at(small_sum_b_1, b) + at(small_sum_b_1, __rust_mir_133)); rewrite(to_integer(at(small_sum_b_1, b) + at(small_sum_b_1, __rust_mir_133)) == to_integer(at(small_sum_b_1, b)) + to_integer(at(small_sum_b_1, __rust_mir_133))); arithmetic() using { to_integer(at(small_sum_b_1, b)) <= 327600; to_integer(at(small_sum_b_1, __rust_mir_133)) <= 327601; } }
 execute_until(assignment(b, 5)); step();
 have to_integer(b) <= 655201 by { simp() using { to_integer(__rust_mir_134) <= 655201; } }
 step(); step(); step(); step(); step(); step(); step(); step();
 have to_integer(b_vec._0[2]) <= 393122 by { simp(); }
 execute_until(assignment(__rust_mir_133, 0));
 have bv == b_vec._0[2] by { simp(); }
 have to_integer(bv) <= 393122 by { rewrite(bv == b_vec._0[2]); assumption(); }
 step();
 have to_integer(__rust_mir_133) <= 393122 by { simp() using { to_integer(bv) <= 393122; } }
 have to_integer(b) + to_integer(__rust_mir_133) <= 4294967295 by { arithmetic() using { to_integer(b) <= 655201; to_integer(__rust_mir_133) <= 393122; } }
 apply(uint32_widened_add_guard_by_integer_bound(b, __rust_mir_133)) using { to_integer(b) + to_integer(__rust_mir_133) <= 4294967295; }
 execute_until(assignment(__rust_mir_134, 0));
 mark small_sum_b_2;
 have to_integer(at(small_sum_b_2, b)) <= 655201 by { simp() using { to_integer(b) <= 655201; } }
 have to_integer(at(small_sum_b_2, __rust_mir_133)) <= 393122 by { simp() using { to_integer(__rust_mir_133) <= 393122; } }
 have to_integer(at(small_sum_b_2, b)) + to_integer(at(small_sum_b_2, __rust_mir_133)) <= 4294967295 by { arithmetic() using { to_integer(at(small_sum_b_2, b)) <= 655201; to_integer(at(small_sum_b_2, __rust_mir_133)) <= 393122; } }
 step();
 have __rust_mir_134 == at(small_sum_b_2, b) + at(small_sum_b_2, __rust_mir_133) by { simp(); }
 apply(uint32_add_to_integer(at(small_sum_b_2, b), at(small_sum_b_2, __rust_mir_133))) using { to_integer(at(small_sum_b_2, b)) + to_integer(at(small_sum_b_2, __rust_mir_133)) <= 4294967295; }
 have to_integer(__rust_mir_134) <= 1048323 by { rewrite(__rust_mir_134 == at(small_sum_b_2, b) + at(small_sum_b_2, __rust_mir_133)); rewrite(to_integer(at(small_sum_b_2, b) + at(small_sum_b_2, __rust_mir_133)) == to_integer(at(small_sum_b_2, b)) + to_integer(at(small_sum_b_2, __rust_mir_133))); arithmetic() using { to_integer(at(small_sum_b_2, b)) <= 655201; to_integer(at(small_sum_b_2, __rust_mir_133)) <= 393122; } }
 execute_until(assignment(b, 5)); step();
 have to_integer(b) <= 1048323 by { simp() using { to_integer(__rust_mir_134) <= 1048323; } }
 step(); step(); step(); step(); step(); step(); step(); step();
 have to_integer(b_vec._0[3]) <= 458643 by { simp(); }
 execute_until(assignment(__rust_mir_133, 0));
 have bv == b_vec._0[3] by { simp(); }
 have to_integer(bv) <= 458643 by { rewrite(bv == b_vec._0[3]); assumption(); }
 step();
 have to_integer(__rust_mir_133) <= 458643 by { simp() using { to_integer(bv) <= 458643; } }
 have to_integer(b) + to_integer(__rust_mir_133) <= 4294967295 by { arithmetic() using { to_integer(b) <= 1048323; to_integer(__rust_mir_133) <= 458643; } }
 apply(uint32_widened_add_guard_by_integer_bound(b, __rust_mir_133)) using { to_integer(b) + to_integer(__rust_mir_133) <= 4294967295; }
 execute_until(assignment(__rust_mir_134, 0));
 mark small_sum_b_3;
 have to_integer(at(small_sum_b_3, b)) <= 1048323 by { simp() using { to_integer(b) <= 1048323; } }
 have to_integer(at(small_sum_b_3, __rust_mir_133)) <= 458643 by { simp() using { to_integer(__rust_mir_133) <= 458643; } }
 have to_integer(at(small_sum_b_3, b)) + to_integer(at(small_sum_b_3, __rust_mir_133)) <= 4294967295 by { arithmetic() using { to_integer(at(small_sum_b_3, b)) <= 1048323; to_integer(at(small_sum_b_3, __rust_mir_133)) <= 458643; } }
 step();
 have __rust_mir_134 == at(small_sum_b_3, b) + at(small_sum_b_3, __rust_mir_133) by { simp(); }
 apply(uint32_add_to_integer(at(small_sum_b_3, b), at(small_sum_b_3, __rust_mir_133))) using { to_integer(at(small_sum_b_3, b)) + to_integer(at(small_sum_b_3, __rust_mir_133)) <= 4294967295; }
 have to_integer(__rust_mir_134) <= 1506966 by { rewrite(__rust_mir_134 == at(small_sum_b_3, b) + at(small_sum_b_3, __rust_mir_133)); rewrite(to_integer(at(small_sum_b_3, b) + at(small_sum_b_3, __rust_mir_133)) == to_integer(at(small_sum_b_3, b)) + to_integer(at(small_sum_b_3, __rust_mir_133))); arithmetic() using { to_integer(at(small_sum_b_3, b)) <= 1048323; to_integer(at(small_sum_b_3, __rust_mir_133)) <= 458643; } }
 execute_until(assignment(b, 5)); step();
 have to_integer(b) <= 1506966 by { simp() using { to_integer(__rust_mir_134) <= 1506966; } }
 step(); step(); step(); step(); step(); step(); step(); step();
 execute_until(loop(5));
 have __rust_mir_138_remaining == 0 by { simp() using { remainder_len == 0u64; } }
 execute_until(assignment(__rust_mir_149, 0));
 have __rust_checked_34 == 65521u32 by { simp(); }
 step();
 have __rust_mir_149 == __rust_checked_32 % __rust_checked_34 by { simp() using {}; }
 have __rust_mir_149 == __rust_checked_32 % 65521u32 by { rewrite(__rust_mir_149 == __rust_checked_32 % __rust_checked_34); rewrite(__rust_checked_34 == 65521u32); normalize(); }
 apply(uint32_remainder_less_than_divisor(__rust_checked_32, 65521u32));
 have __rust_mir_149 < 65521u32 by { rewrite(__rust_mir_149 == __rust_checked_32 % 65521u32); assumption(); }
 apply(uint32_to_integer_bounds(__rust_mir_149));
 apply(uint32_less_than_to_integer(__rust_mir_149, 65521u32)) using { __rust_mir_149 < 65521u32; }
 have to_integer(__rust_mir_149) < 65521 by { simp() using { to_integer(__rust_mir_149) < to_integer(65521u32); } }
 have to_integer(__rust_mir_149) <= 65535 by { arithmetic() using { to_integer(__rust_mir_149) < 65521; } }
 mark small_reduced_a;
 execute_until(assignment(__rust_mir_151, 0));
 have __rust_checked_37 == 65521u32 by { simp(); }
 step();
 have __rust_mir_151 == __rust_checked_35 % __rust_checked_37 by { simp() using {}; }
 have __rust_mir_151 == __rust_checked_35 % 65521u32 by { rewrite(__rust_mir_151 == __rust_checked_35 % __rust_checked_37); rewrite(__rust_checked_37 == 65521u32); normalize(); }
 apply(uint32_remainder_less_than_divisor(__rust_checked_35, 65521u32));
 have __rust_mir_151 < 65521u32 by { rewrite(__rust_mir_151 == __rust_checked_35 % 65521u32); assumption(); }
 apply(uint32_to_integer_bounds(__rust_mir_151));
 apply(uint32_less_than_to_integer(__rust_mir_151, 65521u32)) using { __rust_mir_151 < 65521u32; }
 have to_integer(__rust_mir_151) < 65521 by { simp() using { to_integer(__rust_mir_151) < to_integer(65521u32); } }
 have to_integer(__rust_mir_151) <= 65535 by { arithmetic() using { to_integer(__rust_mir_151) < 65521; } }
 mark small_reduced_b;
 execute();
 have to_integer(self->a) == to_integer(at(small_reduced_a, __rust_mir_149)) by { arithmetic_certificate special {
 premise 0: 0 <= to_integer(at(small_reduced_a, __rust_mir_149)) => 0 <= to_integer(at(small_reduced_a, __rust_mir_149));
 premise 1: to_integer(at(small_reduced_a, __rust_mir_149)) <= 65535 => to_integer(at(small_reduced_a, __rust_mir_149)) <= 65535;
 integer_cast_identity bounds [0, 1] => to_integer(self->a) == to_integer(at(small_reduced_a, __rust_mir_149)); conclusion 0;
 } }
 have to_integer(at(small_reduced_a, __rust_mir_149)) < 65521 by { simp(); }
 have to_integer(self->a) < 65521 by { rewrite(to_integer(self->a) == to_integer(at(small_reduced_a, __rust_mir_149))); assumption(); }
 have to_integer(self->b) == to_integer(at(small_reduced_b, __rust_mir_151)) by { arithmetic_certificate special {
 premise 0: 0 <= to_integer(at(small_reduced_b, __rust_mir_151)) => 0 <= to_integer(at(small_reduced_b, __rust_mir_151));
 premise 1: to_integer(at(small_reduced_b, __rust_mir_151)) <= 65535 => to_integer(at(small_reduced_b, __rust_mir_151)) <= 65535;
 integer_cast_identity bounds [0, 1] => to_integer(self->b) == to_integer(at(small_reduced_b, __rust_mir_151)); conclusion 0;
 } }
 have to_integer(at(small_reduced_b, __rust_mir_151)) < 65521 by { simp(); }
 have to_integer(self->b) < 65521 by { rewrite(to_integer(self->b) == to_integer(at(small_reduced_b, __rust_mir_151))); assumption(); }
 have 0 <= to_integer(self->a) by { rewrite(to_integer(self->a) == to_integer(at(small_reduced_a, __rust_mir_149))); simp() using { 0 <= to_integer(at(small_reduced_a, __rust_mir_149)); } }
 have to_integer(self->a) <= 65535 by { arithmetic() using { to_integer(self->a) < 65521; } }
 have to_integer((int32)self->a) == to_integer(self->a) by { arithmetic_certificate special {
 premise 0: 0 <= to_integer(self->a) => 0 <= to_integer(self->a);
 premise 1: to_integer(self->a) <= 65535 => to_integer(self->a) <= 65535;
 integer_cast_identity bounds [0, 1] => to_integer((int32)self->a) == to_integer(self->a); conclusion 0;
 } }
 have to_integer((int32)self->a) <= to_integer(65520) by { rewrite(to_integer((int32)self->a) == to_integer(self->a)); arithmetic() using { to_integer(self->a) < 65521; } }
 apply(int32_less_equal_of_to_integer((int32)self->a, 65520)) using { to_integer((int32)self->a) <= to_integer(65520); }
 apply(adler_i32_below_mod((int32)self->a)) using { (int32)self->a <= 65520; }
 have self->a < 65521 by { assumption(); }
 have 0 <= to_integer(self->b) by { rewrite(to_integer(self->b) == to_integer(at(small_reduced_b, __rust_mir_151))); simp() using { 0 <= to_integer(at(small_reduced_b, __rust_mir_151)); } }
 have to_integer(self->b) <= 65535 by { arithmetic() using { to_integer(self->b) < 65521; } }
 have to_integer((int32)self->b) == to_integer(self->b) by { arithmetic_certificate special {
 premise 0: 0 <= to_integer(self->b) => 0 <= to_integer(self->b);
 premise 1: to_integer(self->b) <= 65535 => to_integer(self->b) <= 65535;
 integer_cast_identity bounds [0, 1] => to_integer((int32)self->b) == to_integer(self->b); conclusion 0;
 } }
 have to_integer((int32)self->b) <= to_integer(65520) by { rewrite(to_integer((int32)self->b) == to_integer(self->b)); arithmetic() using { to_integer(self->b) < 65521; } }
 apply(int32_less_equal_of_to_integer((int32)self->b, 65520)) using { to_integer((int32)self->b) <= to_integer(65520); }
 apply(adler_i32_below_mod((int32)self->b)) using { (int32)self->b <= 65520; }
 have self->b < 65521 by { assumption(); }
 simp() using { self->a < 65521; self->b < 65521; }
}
