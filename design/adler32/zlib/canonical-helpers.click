import "full-stream-helpers.click";

function zlib_seed_a(word: uint64) -> uint64 { word & 65535u64 }
function zlib_seed_b(word: uint64) -> uint64 { (word >> 16) & 65535u64 }

theorem zlib_general_seeded_batch_concat(bytes: uint8[], prefix: int32, length: int32, a: uint64, b: uint64, a0: uint64, b0: uint64, initial_a: Integer, initial_b: Integer) {
 requires 0 <= initial_a;
 requires initial_a <= 65520;
 requires 0 <= initial_b;
 requires 0 <= prefix;
 requires 0 <= length;
 requires prefix <= 2147483647 - length;
 requires defined(prefix + length);
 requires to_integer(a0) == adler_spec_a(bytes, prefix, initial_a);
 requires to_integer(b0) == adler_spec_b(bytes, prefix, initial_a, initial_b);
 requires to_integer(a) == to_integer(a0) + adler_byte_sum(bytes + prefix, length);
 requires to_integer(b) == to_integer(b0) + to_integer(length) * to_integer(a0) + adler_weighted_sum(bytes + prefix, length, length);
 ensures to_integer(a % 65521u64) == adler_spec_a(bytes, prefix + length, initial_a) by {
  apply(zlib_seeded_reduced_components(bytes + prefix, length, a, b, a0, b0));
  apply(adler_spec_a_concat(bytes, prefix, length, initial_a));
  have to_integer(a % 65521u64) == adler_spec_a(bytes + prefix, length, adler_spec_a(bytes, prefix, initial_a)) by {
   rewrite(adler_spec_a(bytes, prefix, initial_a) == to_integer(a0)); assumption();
  }
  arithmetic() using {
   to_integer(a % 65521u64) == adler_spec_a(bytes + prefix, length, adler_spec_a(bytes, prefix, initial_a));
   adler_spec_a(bytes, prefix + length, initial_a) == adler_spec_a(bytes + prefix, length, adler_spec_a(bytes, prefix, initial_a));
  };
 }
 ensures to_integer(b % 65521u64) == adler_spec_b(bytes, prefix + length, initial_a, initial_b) by {
  apply(zlib_seeded_reduced_components(bytes + prefix, length, a, b, a0, b0));
  apply(adler_spec_b_concat(bytes, prefix, length, initial_a, initial_b));
  have to_integer(b % 65521u64) == adler_spec_b(bytes + prefix, length, adler_spec_a(bytes, prefix, initial_a), adler_spec_b(bytes, prefix, initial_a, initial_b)) by {
   rewrite(adler_spec_a(bytes, prefix, initial_a) == to_integer(a0));
   rewrite(adler_spec_b(bytes, prefix, initial_a, initial_b) == to_integer(b0)); assumption();
  }
  arithmetic() using {
   to_integer(b % 65521u64) == adler_spec_b(bytes + prefix, length, adler_spec_a(bytes, prefix, initial_a), adler_spec_b(bytes, prefix, initial_a, initial_b));
   adler_spec_b(bytes, prefix + length, initial_a, initial_b) == adler_spec_b(bytes + prefix, length, adler_spec_a(bytes, prefix, initial_a), adler_spec_b(bytes, prefix, initial_a, initial_b));
  };
 }
}

theorem zlib_general_raw_seeded_batch_concat(bytes: uint8[], prefix: int32, length: int32, a: uint64, b: uint64, a0: uint64, b0: uint64, initial_a: Integer, initial_b: Integer) {
 requires 0 <= initial_a;
 requires initial_a <= 65520;
 requires 0 <= initial_b;
 requires 0 <= prefix;
 requires 0 <= length;
 requires prefix <= 2147483647 - length;
 requires defined(prefix + length);
 requires a0 <= 1500000u64;
 requires to_integer(a0 % 65521u64) == adler_spec_a(bytes, prefix, initial_a);
 requires to_integer(b0 % 65521u64) == adler_spec_b(bytes, prefix, initial_a, initial_b);
 requires to_integer(a) == to_integer(a0) + adler_byte_sum(bytes + prefix, length);
 requires to_integer(b) == to_integer(b0) + to_integer(length) * to_integer(a0) + adler_weighted_sum(bytes + prefix, length, length);
 ensures to_integer(a % 65521u64) == adler_spec_a(bytes, prefix + length, initial_a) by {
  apply(zlib_seeded_reduced_components(bytes + prefix, length, a, b, a0, b0));
  apply(uint64_to_integer_bounds(a0)); apply(uint64_remainder_to_integer(a0, 65521u64));
  apply(adler_sum_nonnegative(bytes + prefix, length));
  apply(adler_residue_add_left(to_integer(a0), adler_byte_sum(bytes + prefix, length)));
  have adler_spec_a(bytes + prefix, length, to_integer(a0)) == adler_spec_a(bytes + prefix, length, to_integer(a0 % 65521u64)) by {
   unfold(adler_spec_a(bytes + prefix, length, to_integer(a0)));
   unfold(adler_spec_a(bytes + prefix, length, to_integer(a0 % 65521u64)));
   rewrite(to_integer(a0 % 65521u64) == truncating_remainder(to_integer(a0), 65521)); assumption();
  }
  have to_integer(a % 65521u64) == adler_spec_a(bytes + prefix, length, adler_spec_a(bytes, prefix, initial_a)) by {
   rewrite(adler_spec_a(bytes, prefix, initial_a) == to_integer(a0 % 65521u64));
   arithmetic() using {
    to_integer(a % 65521u64) == adler_spec_a(bytes + prefix, length, to_integer(a0));
    adler_spec_a(bytes + prefix, length, to_integer(a0)) == adler_spec_a(bytes + prefix, length, to_integer(a0 % 65521u64));
   };
  }
  apply(adler_spec_a_concat(bytes, prefix, length, initial_a));
  arithmetic() using { to_integer(a % 65521u64) == adler_spec_a(bytes + prefix, length, adler_spec_a(bytes, prefix, initial_a)); adler_spec_a(bytes, prefix + length, initial_a) == adler_spec_a(bytes + prefix, length, adler_spec_a(bytes, prefix, initial_a)); };
 }
 ensures to_integer(b % 65521u64) == adler_spec_b(bytes, prefix + length, initial_a, initial_b) by {
  apply(zlib_seeded_reduced_components(bytes + prefix, length, a, b, a0, b0));
  apply(uint64_to_integer_bounds(a0)); apply(uint64_to_integer_bounds(b0));
  apply(uint64_less_equal_to_integer(a0, 1500000u64));
  apply(uint64_remainder_to_integer(a0, 65521u64)); apply(uint64_remainder_to_integer(b0, 65521u64));
  apply(adler_weighted_nonnegative(bytes + prefix, length));
  apply(int32_less_equal_to_integer(0, length));
  have length <= 2147483647 by normalize();
  apply(int32_less_equal_to_integer(length, 2147483647));
  have to_integer(a0) <= 549755879424 by arithmetic() using { to_integer(a0) <= 1500000; };
  have 0 <= to_integer(length) by simp() using { to_integer(0) <= to_integer(length); };
  have to_integer(length) <= 2147483647 by simp() using { to_integer(length) <= to_integer(2147483647); };
  apply(adler_residue_seed_update(to_integer(a0), to_integer(b0), to_integer(length), adler_weighted_sum(bytes + prefix, length, length)));
  have adler_spec_b(bytes + prefix, length, to_integer(a0), to_integer(b0)) == adler_spec_b(bytes + prefix, length, to_integer(a0 % 65521u64), to_integer(b0 % 65521u64)) by {
   unfold(adler_spec_b(bytes + prefix, length, to_integer(a0), to_integer(b0)));
   unfold(adler_spec_b(bytes + prefix, length, to_integer(a0 % 65521u64), to_integer(b0 % 65521u64)));
   rewrite(to_integer(a0 % 65521u64) == truncating_remainder(to_integer(a0), 65521));
   rewrite(to_integer(b0 % 65521u64) == truncating_remainder(to_integer(b0), 65521)); assumption();
  }
  have to_integer(b % 65521u64) == adler_spec_b(bytes + prefix, length, adler_spec_a(bytes, prefix, initial_a), adler_spec_b(bytes, prefix, initial_a, initial_b)) by {
   rewrite(adler_spec_a(bytes, prefix, initial_a) == to_integer(a0 % 65521u64));
   rewrite(adler_spec_b(bytes, prefix, initial_a, initial_b) == to_integer(b0 % 65521u64));
   arithmetic() using {
    to_integer(b % 65521u64) == adler_spec_b(bytes + prefix, length, to_integer(a0), to_integer(b0));
    adler_spec_b(bytes + prefix, length, to_integer(a0), to_integer(b0)) == adler_spec_b(bytes + prefix, length, to_integer(a0 % 65521u64), to_integer(b0 % 65521u64));
   };
  }
  apply(adler_spec_b_concat(bytes, prefix, length, initial_a, initial_b));
  arithmetic() using { to_integer(b % 65521u64) == adler_spec_b(bytes + prefix, length, adler_spec_a(bytes, prefix, initial_a), adler_spec_b(bytes, prefix, initial_a, initial_b)); adler_spec_b(bytes, prefix + length, initial_a, initial_b) == adler_spec_b(bytes + prefix, length, adler_spec_a(bytes, prefix, initial_a), adler_spec_b(bytes, prefix, initial_a, initial_b)); };
 }
}

theorem zlib_general_components_pack(bytes: uint8[], length: int32, a: uint64, b: uint64, initial_a: Integer, initial_b: Integer) {
 requires to_integer(a % 65521u64) == adler_spec_a(bytes, length, initial_a);
 requires to_integer(b % 65521u64) == adler_spec_b(bytes, length, initial_a, initial_b);
 ensures to_integer((a % 65521u64) | ((b % 65521u64) << 16)) == adler_spec_checksum(bytes, length, initial_a, initial_b) by {
  apply(uint64_remainder_to_integer(a, 65521u64));
  apply(uint64_remainder_to_integer(b, 65521u64));
  apply(integer_positive_divisor_remainder_upper(to_integer(a), 65521));
  apply(integer_positive_divisor_remainder_upper(to_integer(b), 65521));
  have to_integer(a % 65521u64) <= 65535 by arithmetic() using {
   to_integer(a % 65521u64) == truncating_remainder(to_integer(a), 65521);
   truncating_remainder(to_integer(a), 65521) <= 65521 - 1;
  };
  have to_integer(b % 65521u64) <= 65535 by arithmetic() using {
   to_integer(b % 65521u64) == truncating_remainder(to_integer(b), 65521);
   truncating_remainder(to_integer(b), 65521) <= 65521 - 1;
  };
  apply(uint64_to_integer_less_equal_implies_less_equal(a % 65521u64, 65535u64));
  apply(uint64_to_integer_less_equal_implies_less_equal(b % 65521u64, 65535u64));
  apply(uint64_pack_uint16_to_integer(a % 65521u64, b % 65521u64));
  unfold(adler_spec_checksum(bytes, length, initial_a, initial_b));
  arithmetic() using {
   to_integer((a % 65521u64) | ((b % 65521u64) << 16)) == to_integer(a % 65521u64) + 65536 * to_integer(b % 65521u64);
   to_integer(a % 65521u64) == adler_spec_a(bytes, length, initial_a);
   to_integer(b % 65521u64) == adler_spec_b(bytes, length, initial_a, initial_b);
  };
 }
}

// One subtraction is exactly MOD when the original fast path's sum is < 2*BASE.
theorem zlib_reduce_once_below(value: uint64) {
 requires value < 65521u64;
 ensures value <= 65520u64 and to_integer(value) == to_integer(value % 65521u64) by {
  apply(uint64_to_integer_bounds(value));
  apply(uint64_less_than_to_integer(value, 65521u64));
  have to_integer(value) <= 65520 by arithmetic() using { to_integer(value) < 65521; };
  apply(uint64_to_integer_less_equal_implies_less_equal(value, 65520u64));
  have to_integer(value) == 0 * 65521 + to_integer(value) by arithmetic() using {};
  apply(adler_residue_unique(to_integer(value), 0, to_integer(value)));
  apply(uint64_remainder_to_integer(value, 65521u64)); simp();
 }
}
theorem zlib_reduce_once_above(value: uint64) {
 requires 65521u64 <= value;
 requires value <= 131041u64;
 ensures value - 65521u64 <= 65520u64 and to_integer(value - 65521u64) == to_integer(value % 65521u64) by {
  apply(uint64_less_equal_to_integer(65521u64, value));
  apply(uint64_less_equal_to_integer(value, 131041u64));
  apply(uint64_subtract_to_integer(value, 65521u64));
  have 0 <= to_integer(value - 65521u64) by arithmetic() using { 65521 <= to_integer(value); to_integer(value - 65521u64) == to_integer(value) - 65521; };
  have to_integer(value - 65521u64) <= 65520 by arithmetic() using { to_integer(value) <= 131041; to_integer(value - 65521u64) == to_integer(value) - 65521; };
  apply(uint64_to_integer_less_equal_implies_less_equal(value - 65521u64, 65520u64));
  have 0 <= to_integer(value) by arithmetic() using { 65521 <= to_integer(value); };
  have to_integer(value) == 1 * 65521 + to_integer(value - 65521u64) by arithmetic() using { to_integer(value - 65521u64) == to_integer(value) - 65521; };
  apply(adler_residue_unique(to_integer(value), 1, to_integer(value - 65521u64)));
  apply(uint64_remainder_to_integer(value, 65521u64));
  both { assumption(); } and { arithmetic() using {
   to_integer(value % 65521u64) == truncating_remainder(to_integer(value), 65521);
   truncating_remainder(to_integer(value), 65521) == to_integer(value - 65521u64);
  }; }
 }
}

// Exact mathematical observations of the original mask/shift seed decoding.
theorem zlib_seed_bounds(word: uint64) {
 requires zlib_seed_a(word) <= 65520u64;
 requires zlib_seed_b(word) <= 65520u64;
 ensures 0 <= to_integer(zlib_seed_a(word)) and to_integer(zlib_seed_a(word)) <= 65520 and
         0 <= to_integer(zlib_seed_b(word)) and to_integer(zlib_seed_b(word)) <= 65520 by {
  apply(uint64_to_integer_bounds(zlib_seed_a(word)));
  apply(uint64_to_integer_bounds(zlib_seed_b(word)));
  apply(uint64_less_equal_to_integer(zlib_seed_a(word), 65520u64));
  apply(uint64_less_equal_to_integer(zlib_seed_b(word), 65520u64)); simp();
 }
}

// The fast path adds the already-reduced A into B. Residue composition
// connects that order of operations to the shared one-byte specification.
theorem zlib_one_seeded_components(bytes: uint8[], initial_a: Integer, initial_b: Integer, a: uint64, b: uint64) {
 requires 0 <= initial_a;
 requires 0 <= initial_b;
 requires a <= 65520u64;
 requires b <= 65520u64;
 requires to_integer(a) == truncating_remainder(initial_a + zlib_byte_integer(bytes[0]), 65521);
 requires to_integer(b) == truncating_remainder(initial_b + to_integer(a), 65521);
 ensures to_integer(a | (b << 16)) == adler_spec_checksum(bytes, 1, initial_a, initial_b) by {
  apply(adler_sum_empty(bytes, 0)); apply(zlib_component_step(bytes, 0));
  have adler_byte_sum(bytes, 1) == zlib_byte_integer(bytes[0]) by arithmetic() using { adler_byte_sum(bytes, 1) == adler_byte_sum(bytes, 0) + zlib_byte_integer(bytes[0]); adler_byte_sum(bytes, 0) == 0; };
  have adler_weighted_sum(bytes, 1, 1) == zlib_byte_integer(bytes[0]) by arithmetic() using { adler_weighted_sum(bytes, 1, 1) == adler_weighted_sum(bytes, 0, 0) + adler_byte_sum(bytes, 1); adler_weighted_sum(bytes, 0, 0) == 0; adler_byte_sum(bytes, 1) == zlib_byte_integer(bytes[0]); };
  apply(adler_byte_bounds(bytes[0])); apply(zlib_byte_integer_identity(bytes[0]));
  have 0 <= initial_a + zlib_byte_integer(bytes[0]) by arithmetic() using { 0 <= initial_a; 0 <= to_integer((int32)bytes[0]); zlib_byte_integer(bytes[0]) == to_integer((int32)bytes[0]); };
  apply(adler_residue_add_left(initial_a + zlib_byte_integer(bytes[0]), initial_b));
  have (initial_a + zlib_byte_integer(bytes[0])) + initial_b == initial_b + initial_a + zlib_byte_integer(bytes[0]) by arithmetic() using {};
  have truncating_remainder(initial_a + zlib_byte_integer(bytes[0]), 65521) + initial_b == initial_b + to_integer(a) by { rewrite(truncating_remainder(initial_a + zlib_byte_integer(bytes[0]), 65521) == to_integer(a)); arithmetic() using {}; }
  have adler_spec_a(bytes, 1, initial_a) == to_integer(a) by {
   unfold(adler_spec_a(bytes, 1, initial_a)); rewrite(adler_byte_sum(bytes, 1) == zlib_byte_integer(bytes[0])); rewrite(to_integer(a) == truncating_remainder(initial_a + zlib_byte_integer(bytes[0]), 65521)); normalize();
  }
  have adler_spec_b(bytes, 1, initial_a, initial_b) == to_integer(b) by {
   unfold(adler_spec_b(bytes, 1, initial_a, initial_b)); rewrite(adler_weighted_sum(bytes, 1, 1) == zlib_byte_integer(bytes[0]));
   rewrite(initial_b + to_integer(1) * initial_a + zlib_byte_integer(bytes[0]) == (initial_a + zlib_byte_integer(bytes[0])) + initial_b);
   rewrite(truncating_remainder((initial_a + zlib_byte_integer(bytes[0])) + initial_b, 65521) == truncating_remainder(truncating_remainder(initial_a + zlib_byte_integer(bytes[0]), 65521) + initial_b, 65521));
   rewrite(truncating_remainder(initial_a + zlib_byte_integer(bytes[0]), 65521) + initial_b == initial_b + to_integer(a)); rewrite(to_integer(b) == truncating_remainder(initial_b + to_integer(a), 65521)); normalize();
  }
  have a <= 65535u64 by arithmetic() using { a <= 65520u64; };
  have b <= 65535u64 by arithmetic() using { b <= 65520u64; };
  apply(uint64_pack_uint16_to_integer(a, b)); unfold(adler_spec_checksum(bytes, 1, initial_a, initial_b));
  arithmetic() using { to_integer(a | (b << 16)) == to_integer(a) + 65536 * to_integer(b); adler_spec_a(bytes, 1, initial_a) == to_integer(a); adler_spec_b(bytes, 1, initial_a, initial_b) == to_integer(b); };
 }
}

// A scalar short-path prefix fits the existing checked NMAX recurrence.
theorem zlib_short_count_limit(n: int32) {
 requires n <= 14;
 ensures n < 5552 by { arithmetic() using { n <= 14; }; }
}

// The actual C return word can seed another native call with the same state.
theorem zlib_canonical_pack(a: uint64, b: uint64) {
 requires a <= 65520u64;
 requires b <= 65520u64;
 ensures zlib_seed_a(a | (b << 16)) == a and zlib_seed_b(a | (b << 16)) == b by {
  have a <= 65535u64 by arithmetic() using { a <= 65520u64; };
  have b <= 65535u64 by arithmetic() using { b <= 65520u64; };
  apply(uint64_unpack_uint16_low(a, b)); apply(uint64_unpack_uint16_high(a, b));
  unfold(zlib_seed_a(a | (b << 16))); unfold(zlib_seed_b(a | (b << 16))); simp();
 }
 ensures zlib_seed_a(a | (b << 16)) <= 65520u64 and zlib_seed_b(a | (b << 16)) <= 65520u64 and (a | (b << 16)) <= 4294967295u64 by {
  have a <= 65535u64 by arithmetic() using { a <= 65520u64; };
  have b <= 65535u64 by arithmetic() using { b <= 65520u64; };
  apply(uint64_unpack_uint16_low(a, b)); apply(uint64_unpack_uint16_high(a, b));
  unfold(zlib_seed_a(a | (b << 16))); unfold(zlib_seed_b(a | (b << 16)));
  apply(uint64_less_equal_to_integer(a, 65520u64)); apply(uint64_less_equal_to_integer(b, 65520u64));
  apply(uint64_pack_uint16_to_integer(a, b));
  have to_integer(a | (b << 16)) <= to_integer(4294967295u64) by arithmetic() using { to_integer(a | (b << 16)) == to_integer(a) + 65536 * to_integer(b); to_integer(a) <= 65520; to_integer(b) <= 65520; };
  apply(uint64_to_integer_less_equal_implies_less_equal(a | (b << 16), 4294967295u64)); simp();
 }
}

// A checked checksum result carries exactly the canonical state required by
// the next C call. The uint64 observation is injective, including bit 31.
theorem zlib_packed_integer_seed(word: uint64, a: Integer, b: Integer) {
 requires a >= 0; requires a <= 65520;
 requires b >= 0; requires b <= 65520;
 requires to_integer(word) == a + 65536 * b;
 ensures zlib_seed_a(word) <= 65520u64 and zlib_seed_b(word) <= 65520u64 and
         to_integer(zlib_seed_a(word)) == a and to_integer(zlib_seed_b(word)) == b by {
  have a <= 18446744073709551615 by arithmetic() using { a <= 65520; };
  have b <= 18446744073709551615 by arithmetic() using { b <= 65520; };
  apply(integer_to_uint64_round_trip(a)); apply(integer_to_uint64_round_trip(b));
  have to_integer(to_uint64(a)) <= to_integer(65520u64) by arithmetic() using { to_integer(to_uint64(a)) == a; a <= 65520; };
  have to_integer(to_uint64(b)) <= to_integer(65520u64) by arithmetic() using { to_integer(to_uint64(b)) == b; b <= 65520; };
  apply(uint64_to_integer_less_equal_implies_less_equal(to_uint64(a), 65520u64)) using { to_integer(to_uint64(a)) <= to_integer(65520u64); a >= 0; a <= 18446744073709551615; };
  apply(uint64_to_integer_less_equal_implies_less_equal(to_uint64(b), 65520u64)) using { to_integer(to_uint64(b)) <= to_integer(65520u64); b >= 0; b <= 18446744073709551615; };
  apply(zlib_canonical_pack(to_uint64(a), to_uint64(b))) using { to_uint64(a) <= 65520u64; to_uint64(b) <= 65520u64; a >= 0; a <= 18446744073709551615; b >= 0; b <= 18446744073709551615; };
  apply(uint64_less_equal_transitive(to_uint64(a), 65520u64, 65535u64)) using { to_uint64(a) <= 65520u64; 65520u64 <= 65535u64; a >= 0; a <= 18446744073709551615; };
  apply(uint64_less_equal_transitive(to_uint64(b), 65520u64, 65535u64)) using { to_uint64(b) <= 65520u64; 65520u64 <= 65535u64; b >= 0; b <= 18446744073709551615; };
  apply(uint64_pack_uint16_to_integer(to_uint64(a), to_uint64(b))) using { to_uint64(a) <= 65535u64; to_uint64(b) <= 65535u64; a >= 0; a <= 18446744073709551615; b >= 0; b <= 18446744073709551615; };
  have to_integer(word) == to_integer((to_uint64(a) | (to_uint64(b) << 16))) by {
   arithmetic() using {
    to_integer(word) == a + 65536 * b;
    to_integer((to_uint64(a) | (to_uint64(b) << 16))) == to_integer(to_uint64(a)) + 65536 * to_integer(to_uint64(b));
    to_integer(to_uint64(a)) == a; to_integer(to_uint64(b)) == b;
   };
  }
  apply(uint64_to_integer_equal_implies_equal(word, (to_uint64(a) | (to_uint64(b) << 16)))) using { to_integer(word) == to_integer((to_uint64(a) | (to_uint64(b) << 16))); a >= 0; a <= 18446744073709551615; b >= 0; b <= 18446744073709551615; };
  have zlib_seed_a(word) <= 65520u64 by { rewrite(word == (to_uint64(a) | (to_uint64(b) << 16))); assumption(); }
  have zlib_seed_b(word) <= 65520u64 by { rewrite(word == (to_uint64(a) | (to_uint64(b) << 16))); assumption(); }
  have to_integer(zlib_seed_a(word)) == a by { rewrite(word == (to_uint64(a) | (to_uint64(b) << 16))); rewrite(zlib_seed_a((to_uint64(a) | (to_uint64(b) << 16))) == to_uint64(a)); assumption(); }
  have to_integer(zlib_seed_b(word)) == b by { rewrite(word == (to_uint64(a) | (to_uint64(b) << 16))); rewrite(zlib_seed_b((to_uint64(a) | (to_uint64(b) << 16))) == to_uint64(b)); assumption(); }
  simp();
 }
}

// Recover the next native seed from the first call's shared-spec checksum.
theorem zlib_checksum_seed(bytes: uint8[], length: int32, word: uint64, initial_a: Integer, initial_b: Integer) {
 requires 0 <= length;
 requires 0 <= initial_a;
 requires initial_a <= 65520;
 requires 0 <= initial_b;
 requires to_integer(word) == adler_spec_checksum(bytes, length, initial_a, initial_b);
 ensures zlib_seed_a(word) <= 65520u64 and zlib_seed_b(word) <= 65520u64 and
         to_integer(zlib_seed_a(word)) == adler_spec_a(bytes, length, initial_a) and
         to_integer(zlib_seed_b(word)) == adler_spec_b(bytes, length, initial_a, initial_b) by {
  apply(adler_spec_a_canonical(bytes, length, initial_a));
  apply(adler_spec_b_canonical(bytes, length, initial_a, initial_b));
  unfold(adler_spec_checksum(bytes, length, initial_a, initial_b));
  have to_integer(word) == adler_spec_a(bytes, length, initial_a) + 65536 * adler_spec_b(bytes, length, initial_a, initial_b) by arithmetic() using {
   to_integer(word) == adler_spec_checksum(bytes, length, initial_a, initial_b);
   adler_spec_checksum(bytes, length, initial_a, initial_b) == 65536 * adler_spec_b(bytes, length, initial_a, initial_b) + adler_spec_a(bytes, length, initial_a);
  };
  have adler_spec_a(bytes, length, initial_a) >= 0 by arithmetic() using { 0 <= adler_spec_a(bytes, length, initial_a); };
  have adler_spec_b(bytes, length, initial_a, initial_b) >= 0 by arithmetic() using { 0 <= adler_spec_b(bytes, length, initial_a, initial_b); };
  apply(zlib_packed_integer_seed(word, adler_spec_a(bytes, length, initial_a), adler_spec_b(bytes, length, initial_a, initial_b))); assumption();
 }
}
