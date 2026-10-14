import "batch-helpers.click";

// Native DO16 arithmetic for a batch entered with reduced components.
theorem zlib_seeded_component_step(bytes: uint8[], n: int32, a: uint64, b: uint64, value: uint8, a0: uint64, b0: uint64) {
 requires a0 <= 65520u64;
 requires b0 <= 65520u64;
 requires 0 <= n;
 requires n < 5552;
 requires (int32)value == (int32)bytes[n];
 requires to_integer(a) == to_integer(a0) + adler_byte_sum(bytes, n);
 requires to_integer(b) == to_integer(b0) + to_integer(n) * to_integer(a0) + adler_weighted_sum(bytes, n, n);
 requires to_integer(a) <= 65520 + 255 * to_integer(n);
 requires to_integer(b) <= 65520 + 1481280 * to_integer(n);
 ensures to_integer(a + (uint64)(uint32)value) == to_integer(a0) + adler_byte_sum(bytes, n + 1)
     and to_integer(b + (a + (uint64)(uint32)value)) == to_integer(b0) + to_integer(n + 1) * to_integer(a0) + adler_weighted_sum(bytes, n + 1, n + 1)
     and to_integer(a + (uint64)(uint32)value) <= 65520 + 255 * to_integer(n + 1)
     and to_integer(b + (a + (uint64)(uint32)value)) <= 65520 + 1481280 * to_integer(n + 1) by {
  have n <= 5551 by arithmetic() using { n < 5552; };
  have n < 2147483647 by arithmetic() using { n < 5552; };
  apply(int32_less_equal_to_integer(n, 5551));
  have defined(n + 1) by simp();
  apply(int32_add_to_integer(n, 1));
  apply(zlib_byte_u64(value));
  apply(zlib_byte_integer_identity(value));
  apply(zlib_equal_byte_integers(value, bytes[n]));
  apply(zlib_component_step(bytes, n));
  have to_integer(a) + to_integer((uint64)(uint32)value) <= 1481280 by arithmetic() using {
   to_integer(a) <= 65520 + 255 * to_integer(n);
   to_integer(n) <= 5551;
   to_integer((uint64)(uint32)value) == to_integer((int32)value);
   to_integer((int32)value) <= 255;
  };
  have to_integer(a) + to_integer((uint64)(uint32)value) <= 18446744073709551615 by arithmetic() using { to_integer(a) + to_integer((uint64)(uint32)value) <= 1481280; };
  apply(uint64_add_to_integer(a, (uint64)(uint32)value));
  have to_integer(a + (uint64)(uint32)value) <= 1481280 by arithmetic() using {
   to_integer(a + (uint64)(uint32)value) == to_integer(a) + to_integer((uint64)(uint32)value);
   to_integer(a) + to_integer((uint64)(uint32)value) <= 1481280;
  };
  have to_integer(b) + to_integer(a + (uint64)(uint32)value) <= 18446744073709551615 by arithmetic() using {
   to_integer(b) <= 65520 + 1481280 * to_integer(n);
   to_integer(n) <= 5551;
   to_integer(a + (uint64)(uint32)value) <= 1481280;
  };
  apply(uint64_add_to_integer(b, a + (uint64)(uint32)value));
  have to_integer(a + (uint64)(uint32)value) == to_integer(a0) + adler_byte_sum(bytes, n + 1) by arithmetic() using {
   to_integer(a + (uint64)(uint32)value) == to_integer(a) + to_integer((uint64)(uint32)value);
   to_integer(a) == to_integer(a0) + adler_byte_sum(bytes, n);
   to_integer((uint64)(uint32)value) == to_integer((int32)value);
   zlib_byte_integer(value) == to_integer((int32)value);
   zlib_byte_integer(value) == zlib_byte_integer(bytes[n]);
   adler_byte_sum(bytes, n + 1) == adler_byte_sum(bytes, n) + zlib_byte_integer(bytes[n]);
  };
  have to_integer(n + 1) * to_integer(a0) == to_integer(n) * to_integer(a0) + to_integer(a0) by {
   rewrite(to_integer(n + 1) == to_integer(n) + to_integer(1));
   arithmetic_certificate rules {
    integer_polynomial_identity bounds [] => (to_integer(n) + 1) * to_integer(a0) == to_integer(n) * to_integer(a0) + to_integer(a0); conclusion 0;
   }
  }
  have to_integer(b + (a + (uint64)(uint32)value)) == to_integer(b0) + to_integer(n + 1) * to_integer(a0) + adler_weighted_sum(bytes, n + 1, n + 1) by arithmetic() using {
   to_integer(b + (a + (uint64)(uint32)value)) == to_integer(b) + to_integer(a + (uint64)(uint32)value);
   to_integer(b) == to_integer(b0) + to_integer(n) * to_integer(a0) + adler_weighted_sum(bytes, n, n);
   to_integer(a + (uint64)(uint32)value) == to_integer(a0) + adler_byte_sum(bytes, n + 1);
   adler_weighted_sum(bytes, n + 1, n + 1) == adler_weighted_sum(bytes, n, n) + adler_byte_sum(bytes, n + 1);
   to_integer(n + 1) * to_integer(a0) == to_integer(n) * to_integer(a0) + to_integer(a0);
  };
  have to_integer(a + (uint64)(uint32)value) <= 65520 + 255 * to_integer(n + 1) by arithmetic() using {
   to_integer(a + (uint64)(uint32)value) == to_integer(a) + to_integer((uint64)(uint32)value);
   to_integer(a) <= 65520 + 255 * to_integer(n);
   to_integer((uint64)(uint32)value) == to_integer((int32)value);
   to_integer((int32)value) <= 255;
   to_integer(n + 1) == to_integer(n) + to_integer(1);
  };
  have to_integer(b + (a + (uint64)(uint32)value)) <= 65520 + 1481280 * to_integer(n + 1) by arithmetic() using {
   to_integer(b + (a + (uint64)(uint32)value)) == to_integer(b) + to_integer(a + (uint64)(uint32)value);
   to_integer(b) <= 65520 + 1481280 * to_integer(n);
   to_integer(a + (uint64)(uint32)value) <= 1481280;
   to_integer(n + 1) == to_integer(n) + to_integer(1);
  };
  simp();
 }
}

// The original MOD operations return canonical components for this local batch.
theorem zlib_seeded_reduced_components(bytes: uint8[], length: int32, a: uint64, b: uint64, a0: uint64, b0: uint64) {
 requires to_integer(a) == to_integer(a0) + adler_byte_sum(bytes, length);
 requires to_integer(b) == to_integer(b0) + to_integer(length) * to_integer(a0) + adler_weighted_sum(bytes, length, length);
 ensures to_integer(a % 65521u64) == adler_spec_a(bytes, length, to_integer(a0)) by {
  apply(uint64_remainder_to_integer(a, 65521u64));
  unfold(adler_spec_a(bytes, length, to_integer(a0)));
  rewrite(to_integer(a0) + adler_byte_sum(bytes, length) == to_integer(a)); assumption();
 }
 ensures to_integer(b % 65521u64) == adler_spec_b(bytes, length, to_integer(a0), to_integer(b0)) by {
  apply(uint64_remainder_to_integer(b, 65521u64));
  unfold(adler_spec_b(bytes, length, to_integer(a0), to_integer(b0)));
  rewrite(to_integer(b0) + to_integer(length) * to_integer(a0) + adler_weighted_sum(bytes, length, length) == to_integer(b)); assumption();
 }
 ensures a % 65521u64 <= 65520u64 and b % 65521u64 <= 65520u64 by {
  apply(uint64_remainder_to_integer(a, 65521u64));
  apply(uint64_remainder_to_integer(b, 65521u64));
  apply(integer_positive_divisor_remainder_upper(to_integer(a), 65521));
  apply(integer_positive_divisor_remainder_upper(to_integer(b), 65521));
  have to_integer(a % 65521u64) <= 65520 by arithmetic() using {
   to_integer(a % 65521u64) == truncating_remainder(to_integer(a), 65521);
   truncating_remainder(to_integer(a), 65521) <= 65521 - 1;
  };
  have to_integer(b % 65521u64) <= 65520 by arithmetic() using {
   to_integer(b % 65521u64) == truncating_remainder(to_integer(b), 65521);
   truncating_remainder(to_integer(b), 65521) <= 65521 - 1;
  };
  apply(uint64_to_integer_less_equal_implies_less_equal(a % 65521u64, 65520u64));
  apply(uint64_to_integer_less_equal_implies_less_equal(b % 65521u64, 65520u64)); simp();
 }
}

// Connect the next batch's native seeds to the previously processed prefix.
// No C computation is assumed: the raw component equations are premises.
theorem zlib_seeded_batch_concat(bytes: uint8[], prefix: int32, length: int32, a: uint64, b: uint64, a0: uint64, b0: uint64) {
 requires 0 <= prefix;
 requires 0 <= length;
 requires prefix <= 2147483647 - length;
 requires defined(prefix + length);
 requires to_integer(a0) == adler_spec_a(bytes, prefix, 1);
 requires to_integer(b0) == adler_spec_b(bytes, prefix, 1, 0);
 requires to_integer(a) == to_integer(a0) + adler_byte_sum(bytes + prefix, length);
 requires to_integer(b) == to_integer(b0) + to_integer(length) * to_integer(a0) + adler_weighted_sum(bytes + prefix, length, length);
 ensures to_integer(a % 65521u64) == adler_spec_a(bytes, prefix + length, 1) by {
  apply(zlib_seeded_reduced_components(bytes + prefix, length, a, b, a0, b0));
  apply(adler_spec_a_concat(bytes, prefix, length, 1));
  have to_integer(a % 65521u64) == adler_spec_a(bytes + prefix, length, adler_spec_a(bytes, prefix, 1)) by {
   rewrite(adler_spec_a(bytes, prefix, 1) == to_integer(a0)); assumption();
  }
  arithmetic() using {
   to_integer(a % 65521u64) == adler_spec_a(bytes + prefix, length, adler_spec_a(bytes, prefix, 1));
   adler_spec_a(bytes, prefix + length, 1) == adler_spec_a(bytes + prefix, length, adler_spec_a(bytes, prefix, 1));
  };
 }
 ensures to_integer(b % 65521u64) == adler_spec_b(bytes, prefix + length, 1, 0) by {
  apply(zlib_seeded_reduced_components(bytes + prefix, length, a, b, a0, b0));
  apply(adler_spec_b_concat(bytes, prefix, length, 1, 0));
  have to_integer(b % 65521u64) == adler_spec_b(bytes + prefix, length, adler_spec_a(bytes, prefix, 1), adler_spec_b(bytes, prefix, 1, 0)) by {
   rewrite(adler_spec_a(bytes, prefix, 1) == to_integer(a0));
   rewrite(adler_spec_b(bytes, prefix, 1, 0) == to_integer(b0)); assumption();
  }
  arithmetic() using {
   to_integer(b % 65521u64) == adler_spec_b(bytes + prefix, length, adler_spec_a(bytes, prefix, 1), adler_spec_b(bytes, prefix, 1, 0));
   adler_spec_b(bytes, prefix + length, 1, 0) == adler_spec_b(bytes + prefix, length, adler_spec_a(bytes, prefix, 1), adler_spec_b(bytes, prefix, 1, 0));
  };
 }
}
