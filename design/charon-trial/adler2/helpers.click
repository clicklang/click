verifying "src/lib.rs";

struct __rust_q_I6_adler2_I4_algo_I5_U32X4 __rust_q_I6_adler2_I4_algo_T35___rust_q_I6_adler2_I4_algo_I5_U32X4_I4_from(const uint8* bytes, uint64 bytes_len) {
    requires bytes_len >= 4u64;
    views bytes[0..4];
    ensures result._0[0] == bytes[0];
    ensures result._0[1] == bytes[1];
    ensures result._0[2] == bytes[2];
    ensures result._0[3] == bytes[3];
    ensures result._0[0] <= 255u32;
    ensures result._0[1] <= 255u32;
    ensures result._0[2] <= 255u32;
    ensures result._0[3] <= 255u32;
    ensures 0 <= to_integer(result._0[0]);
    ensures to_integer(result._0[0]) <= 255;
    ensures 0 <= to_integer(result._0[1]);
    ensures to_integer(result._0[1]) <= 255;
    ensures 0 <= to_integer(result._0[2]);
    ensures to_integer(result._0[2]) <= 255;
    ensures 0 <= to_integer(result._0[3]);
    ensures to_integer(result._0[3]) <= 255;
} by {
    execute();
    apply(uint32_to_integer_bounds(result._0[0]));
    apply(uint32_less_equal_to_integer(result._0[0], 255u32));
    apply(uint32_to_integer_bounds(result._0[1]));
    apply(uint32_less_equal_to_integer(result._0[1], 255u32));
    apply(uint32_to_integer_bounds(result._0[2]));
    apply(uint32_less_equal_to_integer(result._0[2], 255u32));
    apply(uint32_to_integer_bounds(result._0[3]));
    apply(uint32_less_equal_to_integer(result._0[3], 255u32));
    simp();
}

void __rust_q_I6_adler2_I4_algo_I5_U32X4_add_assign_value_35__rust_q_I6_adler2_I4_algo_I5_U32X4(struct __rust_q_I6_adler2_I4_algo_I5_U32X4* self, struct __rust_q_I6_adler2_I4_algo_I5_U32X4 other) {
    requires to_integer(self->_0[0]) + to_integer(other._0[0]) <= 4294967295;
    requires to_integer(self->_0[1]) + to_integer(other._0[1]) <= 4294967295;
    requires to_integer(self->_0[2]) + to_integer(other._0[2]) <= 4294967295;
    requires to_integer(self->_0[3]) + to_integer(other._0[3]) <= 4294967295;
    owns self->_0[0..4];
    ensures self->_0[0] == old(self->_0[0]) + other._0[0];
    ensures self->_0[1] == old(self->_0[1]) + other._0[1];
    ensures self->_0[2] == old(self->_0[2]) + other._0[2];
    ensures self->_0[3] == old(self->_0[3]) + other._0[3];
    ensures to_integer(self->_0[0]) == to_integer(old(self->_0[0])) + to_integer(other._0[0]);
    ensures 0 <= to_integer(self->_0[0]);
    ensures to_integer(self->_0[1]) == to_integer(old(self->_0[1])) + to_integer(other._0[1]);
    ensures 0 <= to_integer(self->_0[1]);
    ensures to_integer(self->_0[2]) == to_integer(old(self->_0[2])) + to_integer(other._0[2]);
    ensures 0 <= to_integer(self->_0[2]);
    ensures to_integer(self->_0[3]) == to_integer(old(self->_0[3])) + to_integer(other._0[3]);
    ensures 0 <= to_integer(self->_0[3]);
} by {
    apply(uint32_widened_add_guard_by_integer_bound(self->_0[0], other._0[0]));
    apply(uint32_widened_add_guard_by_integer_bound(self->_0[1], other._0[1]));
    apply(uint32_widened_add_guard_by_integer_bound(self->_0[2], other._0[2]));
    apply(uint32_widened_add_guard_by_integer_bound(self->_0[3], other._0[3]));
    execute();
    apply(uint32_add_to_integer(old(self->_0[0]), other._0[0]));
    apply(uint32_to_integer_bounds(self->_0[0]));
    apply(uint32_add_to_integer(old(self->_0[1]), other._0[1]));
    apply(uint32_to_integer_bounds(self->_0[1]));
    apply(uint32_add_to_integer(old(self->_0[2]), other._0[2]));
    apply(uint32_to_integer_bounds(self->_0[2]));
    apply(uint32_add_to_integer(old(self->_0[3]), other._0[3]));
    apply(uint32_to_integer_bounds(self->_0[3]));
    simp();
}

void __rust_q_I6_adler2_I4_algo_I5_U32X4_rem_assign_u32(struct __rust_q_I6_adler2_I4_algo_I5_U32X4* self, uint32 quotient) {
    requires quotient != 0u32;
    owns self->_0[0..4];
    ensures self->_0[0] == old(self->_0[0]) % quotient;
    ensures self->_0[1] == old(self->_0[1]) % quotient;
    ensures self->_0[2] == old(self->_0[2]) % quotient;
    ensures self->_0[3] == old(self->_0[3]) % quotient;
    ensures self->_0[0] < quotient;
    ensures 0 <= to_integer(self->_0[0]);
    ensures to_integer(self->_0[0]) < to_integer(quotient);
    ensures self->_0[1] < quotient;
    ensures 0 <= to_integer(self->_0[1]);
    ensures to_integer(self->_0[1]) < to_integer(quotient);
    ensures self->_0[2] < quotient;
    ensures 0 <= to_integer(self->_0[2]);
    ensures to_integer(self->_0[2]) < to_integer(quotient);
    ensures self->_0[3] < quotient;
    ensures 0 <= to_integer(self->_0[3]);
    ensures to_integer(self->_0[3]) < to_integer(quotient);
} by {
    execute();
    apply(uint32_remainder_less_than_divisor(old(self->_0[0]), quotient));
    have self->_0[0] < quotient by { simp(); }
    apply(uint32_to_integer_bounds(self->_0[0]));
    apply(uint32_less_than_to_integer(self->_0[0], quotient));
    apply(uint32_remainder_less_than_divisor(old(self->_0[1]), quotient));
    have self->_0[1] < quotient by { simp(); }
    apply(uint32_to_integer_bounds(self->_0[1]));
    apply(uint32_less_than_to_integer(self->_0[1], quotient));
    apply(uint32_remainder_less_than_divisor(old(self->_0[2]), quotient));
    have self->_0[2] < quotient by { simp(); }
    apply(uint32_to_integer_bounds(self->_0[2]));
    apply(uint32_less_than_to_integer(self->_0[2], quotient));
    apply(uint32_remainder_less_than_divisor(old(self->_0[3]), quotient));
    have self->_0[3] < quotient by { simp(); }
    apply(uint32_to_integer_bounds(self->_0[3]));
    apply(uint32_less_than_to_integer(self->_0[3], quotient));
    simp();
}

void __rust_q_I6_adler2_I4_algo_I5_U32X4_mul_assign_u32(struct __rust_q_I6_adler2_I4_algo_I5_U32X4* self, uint32 rhs) {
    requires rhs == 0u32 or self->_0[0] <= 4294967295u32 / rhs;
    requires rhs == 0u32 or self->_0[1] <= 4294967295u32 / rhs;
    requires rhs == 0u32 or self->_0[2] <= 4294967295u32 / rhs;
    requires rhs == 0u32 or self->_0[3] <= 4294967295u32 / rhs;
    owns self->_0[0..4];
    ensures self->_0[0] == old(self->_0[0]) * rhs;
    ensures self->_0[1] == old(self->_0[1]) * rhs;
    ensures self->_0[2] == old(self->_0[2]) * rhs;
    ensures self->_0[3] == old(self->_0[3]) * rhs;
} by { execute(); simp(); }

# Empty-input boundary of the original, locked Adler32::compute body.
# The preceding helper bodies and both constant getters are checked here too.
void __rust_q_I6_adler2_I4_algo_T29___rust_q_I6_adler2_I7_Adler32_I7_compute(struct __rust_q_I6_adler2_I7_Adler32* self, const uint8* bytes, uint64 bytes_len) {
 requires bytes_len == 0u64;
 requires self->a == 1;
 requires self->b == 0;
 owns self->a;
 owns self->b;
 views bytes[0..0];
 ensures self->a == 1;
 ensures self->b == 0;
} by {
 # The empty chunk iterators execute no body. Prove the scalar reduction
 # from its checked transition before following lane recombination.
 execute_until(assignment(b, 0)); step();
 have b == 0u32 by { simp(); }
 execute_until(assignment(b, 3));
 have b == 0u32 by { simp(); }
 have __rust_mir_78 == 0u64 by { simp(); }
 step();
 have b == 0u32 by { simp(); }
 execute_until(assignment(b, 4));
 mark scalar_mod;
 have at(scalar_mod, b) == 0u32 by { simp(); }
 step();
 have b == at(scalar_mod, b) % 65521u32 by { simp(); }
 have b == 0u32 by {
 rewrite(b == at(scalar_mod, b) % 65521u32);
 rewrite(at(scalar_mod, b) == 0u32);
 simp();
 }
 # Marks bind the operands before each original lane update. __rust_checked
 # locals are the adapter's actual captured call/arithmetic operands, not
 # proof counters. These names are checked against the frozen import.
 execute_until(assignment(__rust_mir_94, 0));
 mark add_lane_1;
 have at(add_lane_1, b_vec._0[1]) == 0u32 by { simp(); }
 have at(add_lane_1, __rust_mir_89) == 65521u32 by { simp(); }
 step();
 mark stored_lane_1;
 have __rust_mir_94 == at(add_lane_1, b_vec._0[1]) + at(add_lane_1, __rust_mir_89) by { simp(); }
 have at(stored_lane_1, __rust_mir_94) == 65521u32 by {
  rewrite(__rust_mir_94 == at(add_lane_1, b_vec._0[1]) + at(add_lane_1, __rust_mir_89));
  rewrite(at(add_lane_1, b_vec._0[1]) == 0u32);
  rewrite(at(add_lane_1, __rust_mir_89) == 65521u32);
  simp();
 }
 execute_until(assignment(__rust_mir_98, 0));
 have b_vec._0[1] == at(stored_lane_1, __rust_mir_94) by { simp(); }
 have b_vec._0[1] == 65521u32 by {
  rewrite(b_vec._0[1] == at(stored_lane_1, __rust_mir_94));
  rewrite(at(stored_lane_1, __rust_mir_94) == 65521u32);
  simp();
 }
 execute_until(assignment(__rust_mir_99, 0));
 mark subtract_double;
 have at(subtract_double, __rust_checked_53) == 65521u32 by { simp(); }
 have at(subtract_double, __rust_checked_54) == 0u32 by { simp(); }
 step();
 have __rust_mir_99 == at(subtract_double, __rust_checked_53) - at(subtract_double, __rust_checked_54) by { simp(); }
 have __rust_mir_99 == 65521u32 by {
  rewrite(__rust_mir_99 == at(subtract_double, __rust_checked_53) - at(subtract_double, __rust_checked_54));
  rewrite(at(subtract_double, __rust_checked_53) == 65521u32);
  rewrite(at(subtract_double, __rust_checked_54) == 0u32);
  simp();
 }
 execute_until(assignment(__rust_mir_100, 0));
 mark double_lane;
 have at(double_lane, __rust_mir_96) == 65521u32 by { simp(); }
 step();
 have __rust_mir_100 == at(double_lane, __rust_mir_96) * 2u32 by { simp(); }
 have __rust_mir_100 == 131042u32 by {
  rewrite(__rust_mir_100 == at(double_lane, __rust_mir_96) * 2u32);
  rewrite(at(double_lane, __rust_mir_96) == 65521u32);
  simp();
 }
 execute_until(assignment(__rust_mir_102, 0));
 mark add_lane_2;
 have at(add_lane_2, b_vec._0[2]) == 0u32 by { simp(); }
 have at(add_lane_2, __rust_mir_95) == 131042u32 by { simp(); }
 step();
 mark stored_lane_2;
 have __rust_mir_102 == at(add_lane_2, b_vec._0[2]) + at(add_lane_2, __rust_mir_95) by { simp(); }
 have at(stored_lane_2, __rust_mir_102) == 131042u32 by {
  rewrite(__rust_mir_102 == at(add_lane_2, b_vec._0[2]) + at(add_lane_2, __rust_mir_95));
  rewrite(at(add_lane_2, b_vec._0[2]) == 0u32);
  rewrite(at(add_lane_2, __rust_mir_95) == 131042u32);
  simp();
 }
 execute_until(assignment(__rust_mir_106, 0));
 have b_vec._0[2] == at(stored_lane_2, __rust_mir_102) by { simp(); }
 have b_vec._0[2] == 131042u32 by {
  rewrite(b_vec._0[2] == at(stored_lane_2, __rust_mir_102));
  rewrite(at(stored_lane_2, __rust_mir_102) == 131042u32);
  simp();
 }
 execute_until(assignment(__rust_mir_107, 0));
 mark subtract_triple;
 have at(subtract_triple, __rust_checked_64) == 65521u32 by { simp(); }
 have at(subtract_triple, __rust_checked_65) == 0u32 by { simp(); }
 step();
 have __rust_mir_107 == at(subtract_triple, __rust_checked_64) - at(subtract_triple, __rust_checked_65) by { simp(); }
 have __rust_mir_107 == 65521u32 by {
  rewrite(__rust_mir_107 == at(subtract_triple, __rust_checked_64) - at(subtract_triple, __rust_checked_65));
  rewrite(at(subtract_triple, __rust_checked_64) == 65521u32);
  rewrite(at(subtract_triple, __rust_checked_65) == 0u32);
  simp();
 }
 execute_until(assignment(__rust_mir_108, 0));
 mark triple_lane;
 have at(triple_lane, __rust_mir_104) == 65521u32 by { simp(); }
 step();
 have __rust_mir_108 == at(triple_lane, __rust_mir_104) * 3u32 by { simp(); }
 have __rust_mir_108 == 196563u32 by {
  rewrite(__rust_mir_108 == at(triple_lane, __rust_mir_104) * 3u32);
  rewrite(at(triple_lane, __rust_mir_104) == 65521u32);
  simp();
 }
 execute_until(assignment(__rust_mir_110, 0));
 mark add_lane_3;
 have at(add_lane_3, b_vec._0[3]) == 0u32 by { simp(); }
 have at(add_lane_3, __rust_mir_103) == 196563u32 by { simp(); }
 step();
 mark stored_lane_3;
 have __rust_mir_110 == at(add_lane_3, b_vec._0[3]) + at(add_lane_3, __rust_mir_103) by { simp(); }
 have at(stored_lane_3, __rust_mir_110) == 196563u32 by {
  rewrite(__rust_mir_110 == at(add_lane_3, b_vec._0[3]) + at(add_lane_3, __rust_mir_103));
  rewrite(at(add_lane_3, b_vec._0[3]) == 0u32);
  rewrite(at(add_lane_3, __rust_mir_103) == 196563u32);
  simp();
 }
 execute_until(assignment(__rust_mir_113, 0));
 have b_vec._0[3] == at(stored_lane_3, __rust_mir_110) by { simp(); }
 have b_vec._0[3] == 196563u32 by {
  rewrite(b_vec._0[3] == at(stored_lane_3, __rust_mir_110));
  rewrite(at(stored_lane_3, __rust_mir_110) == 196563u32);
  simp();
 }
 execute_until(loop(3));
 have a == 1u32 by { simp(); }
 have b == 0u32 by { simp(); }
 have a_vec._0[0] == 0u32 by { simp(); }
 have a_vec._0[1] == 0u32 by { simp(); }
 have a_vec._0[2] == 0u32 by { simp(); }
 have a_vec._0[3] == 0u32 by { simp(); }
 have b_vec._0[0] == 0u32 by { simp(); }
 have b_vec._0[1] == 65521u32 by { simp(); }
 have b_vec._0[2] == 131042u32 by { simp(); }
 have b_vec._0[3] == 196563u32 by { simp(); }
 # Read-only array iteration sums all four original lanes in order.
 mark before_sum_a;
 have at(before_sum_a, a) == 1u32 by { simp(); }
 have at(before_sum_a, a_vec._0[0]) == 0u32 by { simp(); }
 have at(before_sum_a, a_vec._0[1]) == 0u32 by { simp(); }
 have at(before_sum_a, a_vec._0[2]) == 0u32 by { simp(); }
 have at(before_sum_a, a_vec._0[3]) == 0u32 by { simp(); }
 execute_until(loop(4));
 have a == at(before_sum_a, a) + at(before_sum_a, a_vec._0[0]) + at(before_sum_a, a_vec._0[1]) + at(before_sum_a, a_vec._0[2]) + at(before_sum_a, a_vec._0[3]) by { simp(); }
 have a == 1u32 by {
 rewrite(a == at(before_sum_a, a) + at(before_sum_a, a_vec._0[0]) + at(before_sum_a, a_vec._0[1]) + at(before_sum_a, a_vec._0[2]) + at(before_sum_a, a_vec._0[3]));
 rewrite(at(before_sum_a, a) == 1u32);
 rewrite(at(before_sum_a, a_vec._0[0]) == 0u32);
 rewrite(at(before_sum_a, a_vec._0[1]) == 0u32);
 rewrite(at(before_sum_a, a_vec._0[2]) == 0u32);
 rewrite(at(before_sum_a, a_vec._0[3]) == 0u32);
 simp();
 }
 mark before_sum_b;
 have at(before_sum_b, b) == 0u32 by { simp(); }
 have at(before_sum_b, b_vec._0[0]) == 0u32 by { simp(); }
 have at(before_sum_b, b_vec._0[1]) == 65521u32 by { simp(); }
 have at(before_sum_b, b_vec._0[2]) == 131042u32 by { simp(); }
 have at(before_sum_b, b_vec._0[3]) == 196563u32 by { simp(); }
 execute_until(loop(5));
 have b == at(before_sum_b, b) + at(before_sum_b, b_vec._0[0]) + at(before_sum_b, b_vec._0[1]) + at(before_sum_b, b_vec._0[2]) + at(before_sum_b, b_vec._0[3]) by { simp(); }
 have b == 393126u32 by {
 rewrite(b == at(before_sum_b, b) + at(before_sum_b, b_vec._0[0]) + at(before_sum_b, b_vec._0[1]) + at(before_sum_b, b_vec._0[2]) + at(before_sum_b, b_vec._0[3]));
 rewrite(at(before_sum_b, b) == 0u32);
 rewrite(at(before_sum_b, b_vec._0[0]) == 0u32);
 rewrite(at(before_sum_b, b_vec._0[1]) == 65521u32);
 rewrite(at(before_sum_b, b_vec._0[2]) == 131042u32);
 rewrite(at(before_sum_b, b_vec._0[3]) == 196563u32);
 simp();
 }
 # Reduce before narrowing to u16; retain only these checked values in
 # the final store closers.
 execute_until(assignment(__rust_mir_149, 0));
 mark output_a;
 have at(output_a, __rust_mir_150) == 1u32 by { simp(); }
 step();
 have at(output_a, __rust_checked_32) == 1u32 by { simp(); }
 have at(output_a, __rust_checked_34) == 65521u32 by { simp(); }
 have __rust_mir_149 == at(output_a, __rust_checked_32) % at(output_a, __rust_checked_34) by { simp(); }
 have __rust_mir_149 == 1u32 by {
 rewrite(__rust_mir_149 == at(output_a, __rust_checked_32) % at(output_a, __rust_checked_34));
 rewrite(at(output_a, __rust_checked_32) == 1u32);
 rewrite(at(output_a, __rust_checked_34) == 65521u32);
 simp();
 }
 mark reduced_a;
 have at(reduced_a, __rust_mir_149) == 1u32 by { simp(); }
 execute_until(assignment(__rust_mir_151, 0));
 mark output_b;
 have at(output_b, __rust_mir_152) == 393126u32 by { simp(); }
 step();
 have at(output_b, __rust_checked_35) == 393126u32 by { simp(); }
 have at(output_b, __rust_checked_37) == 65521u32 by { simp(); }
 have __rust_mir_151 == at(output_b, __rust_checked_35) % at(output_b, __rust_checked_37) by { simp(); }
 have __rust_mir_151 == 0u32 by {
 rewrite(__rust_mir_151 == at(output_b, __rust_checked_35) % at(output_b, __rust_checked_37));
 rewrite(at(output_b, __rust_checked_35) == 393126u32);
 rewrite(at(output_b, __rust_checked_37) == 65521u32);
 simp();
 }
 mark reduced_b;
 have at(reduced_b, __rust_mir_151) == 0u32 by { simp(); }
 execute();
 have self->a == 1 by { simp() using { at(reduced_a, __rust_mir_149) == 1u32; } }
 have self->b == 0 by { simp() using { at(reduced_b, __rust_mir_151) == 0u32; } }
 simp() using { self->a == 1; self->b == 0; }
}

uint32 __rust_q_I6_adler2_I4_algo_T29___rust_q_I6_adler2_I7_Adler32_I7_compute_I3_MOD() { ensures result == 65521u32; } by { execute(); simp(); }
uint64 __rust_q_I6_adler2_I4_algo_T29___rust_q_I6_adler2_I7_Adler32_I7_compute_I10_CHUNK_SIZE() { ensures result == 22208u64; } by { execute(); simp(); }
