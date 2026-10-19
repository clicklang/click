target "x86_64-unknown-linux-gnu";
verifying "../../vendor/zlib-1.3.1/adler32.c";
import "full-stream-helpers.click";
uint64 adler32_z(uint64 adler, const uint8* buf, uint64 len) {
 requires adler == 1u64;
 requires len <= 2147483647u64;
 requires buf != 0;
 views buf[0u64..len];
 ensures to_integer(result) == adler_spec_checksum(old(buf), old((int32)(uint32)len), 1, 0);
 ensures forall (k: uint64) { k < old(len) implies old(buf)[k] == old(buf[k]) };
  } by {
 // The original one-byte fast return precedes all batch and short-loop paths.
 if len == 1u64 {
  have old((int32)(uint32)len) == 1 by simp();
  have viewable(buf[0u64..1u64]) by simp();

 execute_until(assignment(adler, 0)); step();
 have adler == 1u64 by { simp(); }
 have sum2 == 0u64 by { simp(); }
 apply(zlib_byte_u64(buf[0]));
 have adler + (uint64)buf[0] < 65521u64 by { rewrite(adler == 1u64); arithmetic() using { (uint64)buf[0] <= 255u64; }; }
 execute_until(assignment(adler, 1)); step();
 have adler == 1u64 + (uint64)(uint32)buf[0] by { simp(); }
 have adler <= 256u64 by { arithmetic() using { (uint64)(uint32)buf[0] <= 255u64; adler == 1u64 + (uint64)(uint32)buf[0]; }; }
 have adler < 65521u64 by { arithmetic() using { adler <= 256u64; }; }
 apply(uint64_less_than_implies_not_greater_equal(adler, 65521u64));
 execute_until(assignment(sum2, 1)); step();
 have sum2 == adler by { simp(); }
 have sum2 <= 256u64 by { rewrite(sum2 == adler); assumption(); }
 have sum2 < 65521u64 by { arithmetic() using { sum2 <= 256u64; }; }
 apply(uint64_less_than_implies_not_greater_equal(sum2, 65521u64));
 have adler <= 65535u64 by { arithmetic() using { adler <= 256u64; }; }
 have sum2 <= 65535u64 by { arithmetic() using { sum2 <= 256u64; }; }
 apply(uint64_pack_uint16_to_integer(adler, sum2));
 have to_integer(1u64) + to_integer((uint64)(uint32)buf[0]) <= 18446744073709551615 by { arithmetic() using { to_integer((uint64)(uint32)buf[0]) == to_integer((int32)buf[0]); to_integer((int32)buf[0]) <= 255; }; }
 apply(uint64_add_to_integer(1u64, (uint64)(uint32)buf[0]));
 have to_integer(adler) == 1 + to_integer((int32)buf[0]) by { rewrite(adler == 1u64 + (uint64)(uint32)buf[0]); rewrite(to_integer(1u64 + (uint64)(uint32)buf[0]) == to_integer(1u64) + to_integer((uint64)(uint32)buf[0])); rewrite(to_integer((uint64)(uint32)buf[0]) == to_integer((int32)buf[0])); simp(); }
 apply(adler_spec_one(buf));
 have 0 <= 1 + to_integer((int32)buf[0]) by { arithmetic() using { 0 <= to_integer((int32)buf[0]); }; }
 have 1 + to_integer((int32)buf[0]) < 65521 by { arithmetic() using { to_integer((int32)buf[0]) <= 255; }; }
 have 1 + to_integer((int32)buf[0]) <= 65520 by { arithmetic() using { to_integer((int32)buf[0]) <= 255; }; }
 have 1 + to_integer((int32)buf[0]) == 0 * 65521 + (1 + to_integer((int32)buf[0])) by { arithmetic() using {}; }
 apply(adler_residue_unique(1 + to_integer((int32)buf[0]), 0, 1 + to_integer((int32)buf[0])));

 apply(zlib_full_pack_order(1 + to_integer((int32)buf[0])));
 have to_integer(adler | (sum2 << 16)) == adler_spec_checksum(buf, 1, 1, 0) by {
  unfold(adler_spec_checksum(buf, 1, 1, 0));
  rewrite(adler_spec_a(buf, 1, 1) == truncating_remainder(1 + to_integer((int32)buf[0]), 65521));
  rewrite(adler_spec_b(buf, 1, 1, 0) == truncating_remainder(1 + to_integer((int32)buf[0]), 65521));
  rewrite(truncating_remainder(1 + to_integer((int32)buf[0]), 65521) == 1 + to_integer((int32)buf[0]));
  rewrite(to_integer(adler | (sum2 << 16)) == to_integer(adler) + 65536 * to_integer(sum2));
  rewrite(sum2 == adler);
  rewrite(to_integer(adler) == 1 + to_integer((int32)buf[0]));
  assumption();
 }
 have to_integer(adler | (sum2 << 16)) == adler_spec_checksum(old(buf), old((int32)(uint32)len), 1, 0) by {
  rewrite(old((int32)(uint32)len) == 1);
  simp() using { to_integer(adler | (sum2 << 16)) == adler_spec_checksum(buf, 1, 1, 0); };
 }
 execute(); simp();

 } else {
  if len <= 15u64 {

 have viewable(buf[0u64..len]) by simp();
 execute_until(loop(0));
 have viewable(buf[0u64..len]) by simp();
 loop {
  decreases to_integer(len);
  views buf[0u64..len];
  invariant to_integer(len) <= 15;
  invariant to_integer(old(len)) <= 15;
  invariant len <= old(len);
  invariant buf == old(buf) + (old(len) - len);
  invariant viewable(buf[0u64..len]);
  invariant old(len) - len <= 15u64;
  invariant to_integer(adler) == 1 + adler_byte_sum(old(buf), zlib_prefix_count(old(len), len));
  invariant to_integer(sum2) == to_integer(zlib_prefix_count(old(len), len)) + adler_weighted_sum(old(buf), zlib_prefix_count(old(len), len), zlib_prefix_count(old(len), len));
  invariant 1 <= to_integer(adler);
  invariant to_integer(adler) <= 1 + 255 * (to_integer(old(len)) - to_integer(len));
  invariant to_integer(adler) <= 3826;
  invariant 0 <= to_integer(sum2);
  invariant to_integer(sum2) <= 3826 * (to_integer(old(len)) - to_integer(len));
  invariant to_integer(sum2) <= 57390;
  initialize by {
   apply(uint64_less_equal_to_integer(len, 15u64));
   have adler == 1u64 by simp();
   have sum2 == 0u64 by simp();
   apply(adler_sum_empty(old(buf), 0));
   have old(len) - len == 0u64 by simp();
   have to_integer(adler) == 1 by { simp() using { adler == 1u64; }; }
   have to_integer(sum2) == 0 by { simp() using { sum2 == 0u64; }; }
   have 1 <= to_integer(adler) by arithmetic() using { to_integer(adler) == 1; };
   have to_integer(adler) <= 3826 by arithmetic() using { to_integer(adler) == 1; };
   have 0 <= to_integer(sum2) by arithmetic() using { to_integer(sum2) == 0; };
   have to_integer(sum2) <= 57390 by arithmetic() using { to_integer(sum2) == 0; };
   have to_integer(old(len)) == to_integer(len) by simp();
   have zlib_prefix_count(old(len), len) == 0 by {
    unfold(zlib_prefix_count(old(len), len));
    simp();
   }
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), zlib_prefix_count(old(len), len)) by {
    rewrite(zlib_prefix_count(old(len), len) == 0);
    rewrite(adler_byte_sum(old(buf), 0) == 0);
    simp() using { to_integer(adler) == 1; };
   }
   have to_integer(sum2) == to_integer(zlib_prefix_count(old(len), len)) + adler_weighted_sum(old(buf), zlib_prefix_count(old(len), len), zlib_prefix_count(old(len), len)) by {
    rewrite(zlib_prefix_count(old(len), len) == 0);
    rewrite(adler_weighted_sum(old(buf), 0, 0) == 0);
    simp() using { to_integer(sum2) == 0; };
   }
   have to_integer(adler) <= 1 + 255 * (to_integer(old(len)) - to_integer(len)) by arithmetic() using { to_integer(adler) == 1; to_integer(old(len)) == to_integer(len); };
   have to_integer(sum2) <= 3826 * (to_integer(old(len)) - to_integer(len)) by arithmetic() using { to_integer(sum2) == 0; to_integer(old(len)) == to_integer(len); };
   simp();
  }
  preserve by {
   if len == 0u64 {
    have old(len) - len == old(len) by simp();
    have zlib_prefix_count(old(len), len) == old((int32)(uint32)len) by {
     unfold(zlib_prefix_count(old(len), len));
     simp();
    }
    have to_integer(adler) == 1 + adler_byte_sum(old(buf), old((int32)(uint32)len)) by {
     simp() using { to_integer(adler) == 1 + adler_byte_sum(old(buf), zlib_prefix_count(old(len), len)); zlib_prefix_count(old(len), len) == old((int32)(uint32)len); };
    }
    have to_integer(sum2) == to_integer(old((int32)(uint32)len)) + adler_weighted_sum(old(buf), old((int32)(uint32)len), old((int32)(uint32)len)) by {
     simp() using { to_integer(sum2) == to_integer(zlib_prefix_count(old(len), len)) + adler_weighted_sum(old(buf), zlib_prefix_count(old(len), len), zlib_prefix_count(old(len), len)); zlib_prefix_count(old(len), len) == old((int32)(uint32)len); };
    }
    step(); step(); step(); step();
    have __click_call_result1 == 0u64 by assumption();
    step();
   } else {
    have 0u64 <= len by normalize();
    have 0u64 < len by {
     if 0u64 < len { assumption(); } else {
      apply(uint64_less_equal_and_not_less_than_implies_equal(0u64, len));
      have len == 0u64 by { rewrite(0u64 == len); normalize(); }
      contradiction(len == 0u64);
     }
    }
   apply(uint64_to_integer_bounds(len));
   apply(uint64_less_than_to_integer(0u64, len));
   have to_integer(1u64) <= to_integer(len) by arithmetic() using { to_integer(0u64) < to_integer(len); };
   apply(uint64_to_integer_less_equal_implies_less_equal(1u64, len));
   apply(uint64_subtract_to_integer(len, 1u64));
   step(); step();
   have 0u64 < len by assumption();
   apply(uint64_to_integer_less_equal_implies_less_equal(len, 15u64));
   have 0u64 <= len by normalize();
   have 0u64 <= len - 0u64 by normalize();
   have viewable(buf[0u64..1u64]) by simp();
   have viewable(buf[0u64..len]) by simp();
   mark before_decrement;
   step(); step(); step();
   have to_integer(len) == at(before_decrement, to_integer(len)) - 1 by assumption();
   have to_integer(len) <= 15 by arithmetic() using { to_integer(len) == at(before_decrement, to_integer(len)) - 1; at(before_decrement, to_integer(len)) <= 15; };
   have 0 <= to_integer(len) by arithmetic() using { to_integer(len) == at(before_decrement, to_integer(len)) - 1; to_integer(1u64) <= at(before_decrement, to_integer(len)); };
   have to_integer(len) < at(before_decrement, to_integer(len)) by arithmetic() using { to_integer(len) == at(before_decrement, to_integer(len)) - 1; };
   execute_until(assignment(adler, 3));
   have __click_call_result0 == at(before_decrement, buf) by simp();
   have viewable(__click_call_result0[0u64..1u64]) by {
    simp() using { __click_call_result0 == at(before_decrement, buf); at(before_decrement, viewable(buf[0u64..1u64])); };
   }
   have __click_call_result0 == old(buf) + (old(len) - at(before_decrement, len)) by simp();
   have at(before_decrement, len) <= old(len) by assumption();
   apply(uint64_less_equal_to_integer(at(before_decrement, len), old(len)));
   apply(uint64_subtract_to_integer(old(len), at(before_decrement, len)));
   have to_integer(old(len) - at(before_decrement, len)) < to_integer(old(len)) by arithmetic() using {
    to_integer(old(len) - at(before_decrement, len)) == to_integer(old(len)) - at(before_decrement, to_integer(len));
    to_integer(1u64) <= at(before_decrement, to_integer(len));
   };
   apply(uint64_to_integer_less_than_implies_less_than(old(len) - at(before_decrement, len), old(len)));
   apply(uint64_to_integer_less_equal_implies_less_equal(old(len), 15u64));
   have to_integer(old(len) - at(before_decrement, len)) <= 14 by arithmetic() using {
    to_integer(old(len) - at(before_decrement, len)) == to_integer(old(len)) - at(before_decrement, to_integer(len));
    to_integer(old(len)) <= 15;
    to_integer(1u64) <= at(before_decrement, to_integer(len));
   };
   apply(uint64_to_integer_less_equal_implies_less_equal(old(len) - at(before_decrement, len), 14u64));
   have old(len) - at(before_decrement, len) <= 22208u64 by arithmetic() using { old(len) - at(before_decrement, len) <= 14u64; };
   have old(len) - at(before_decrement, len) <= 15u64 by arithmetic() using { old(len) - at(before_decrement, len) <= 14u64; };
   apply(zlib_prefix_pointer(old(buf), old(len), at(before_decrement, len)));
   have __click_call_result0 == old(buf) + zlib_prefix_count(old(len), at(before_decrement, len)) by simp() using {
    __click_call_result0 == old(buf) + (old(len) - at(before_decrement, len));
    old(buf) + (old(len) - at(before_decrement, len)) == old(buf) + zlib_prefix_count(old(len), at(before_decrement, len));
   };
   have __click_call_result0[0] == old(buf)[zlib_prefix_count(old(len), at(before_decrement, len))] by simp() using {
    __click_call_result0 == old(buf) + zlib_prefix_count(old(len), at(before_decrement, len));
   };
   apply(zlib_byte_u64(__click_call_result0[0]));
   apply(zlib_byte_integer_identity(__click_call_result0[0]));
   have to_integer(adler) <= 3571 by arithmetic() using {
    to_integer(adler) <= 1 + 255 * (to_integer(old(len)) - at(before_decrement, to_integer(len)));
    to_integer(old(len)) <= 15;
    to_integer(1u64) <= at(before_decrement, to_integer(len));
   };
   have to_integer(adler) + to_integer((uint64)(uint32)__click_call_result0[0]) <= 18446744073709551615 by arithmetic() using {
    to_integer(adler) <= 3571;
    to_integer((uint64)(uint32)__click_call_result0[0]) == to_integer((int32)__click_call_result0[0]);
    to_integer((int32)__click_call_result0[0]) <= 255;
   };
   apply(uint64_add_to_integer(adler, (uint64)(uint32)__click_call_result0[0]));
   mark before_add;
   step();
   have adler == at(before_add, adler + (uint64)(uint32)__click_call_result0[0]) by simp();
   have to_integer(adler) == at(before_add, to_integer(adler + (uint64)(uint32)__click_call_result0[0])) by simp() using { adler == at(before_add, adler + (uint64)(uint32)__click_call_result0[0]); };
   have to_integer(adler) == at(before_add, to_integer(adler)) + at(before_add, to_integer((int32)__click_call_result0[0])) by arithmetic() using {
    to_integer(adler) == at(before_add, to_integer(adler + (uint64)(uint32)__click_call_result0[0]));
    at(before_add, to_integer(adler + (uint64)(uint32)__click_call_result0[0])) == at(before_add, to_integer(adler)) + at(before_add, to_integer((uint64)(uint32)__click_call_result0[0]));
    at(before_add, to_integer((uint64)(uint32)__click_call_result0[0])) == at(before_add, to_integer((int32)__click_call_result0[0]));
   };
   have 1 <= to_integer(adler) by arithmetic() using {
    1 <= at(before_add, to_integer(adler));
    0 <= at(before_add, to_integer((int32)__click_call_result0[0]));
    to_integer(adler) == at(before_add, to_integer(adler)) + at(before_add, to_integer((int32)__click_call_result0[0]));
   };
   have to_integer(adler) <= 1 + 255 * (to_integer(old(len)) - to_integer(len)) by arithmetic() using {
    at(before_add, to_integer(adler)) <= 1 + 255 * (to_integer(old(len)) - at(before_decrement, to_integer(len)));
    at(before_add, to_integer((int32)__click_call_result0[0])) <= 255;
    to_integer(adler) == at(before_add, to_integer(adler)) + at(before_add, to_integer((int32)__click_call_result0[0]));
    to_integer(len) == at(before_decrement, to_integer(len)) - 1;
   };
   have to_integer(adler) <= 3826 by arithmetic() using {
    at(before_add, to_integer(adler)) <= 3571;
    at(before_add, to_integer((int32)__click_call_result0[0])) <= 255;
    to_integer(adler) == at(before_add, to_integer(adler)) + at(before_add, to_integer((int32)__click_call_result0[0]));
   };
   have to_integer(sum2) + to_integer(adler) <= 18446744073709551615 by arithmetic() using {
    to_integer(sum2) <= 57390;
    to_integer(adler) <= 3826;
   };
   apply(uint64_add_to_integer(sum2, adler));
   mark before_sum;
   execute_until(back_edge());
   have to_integer(sum2) == at(before_sum, to_integer(sum2)) + to_integer(adler) by simp();
   have 0 <= to_integer(sum2) by apply(uint64_to_integer_bounds(sum2));
   have to_integer(sum2) <= 3826 * (to_integer(old(len)) - to_integer(len)) by arithmetic() using {
    at(before_sum, to_integer(sum2)) <= 3826 * (to_integer(old(len)) - at(before_decrement, to_integer(len)));
    to_integer(adler) <= 3826;
    to_integer(sum2) == at(before_sum, to_integer(sum2)) + to_integer(adler);
    to_integer(len) == at(before_decrement, to_integer(len)) - 1;
   };
   have to_integer(sum2) <= 57390 by arithmetic() using {
    to_integer(sum2) <= 3826 * (to_integer(old(len)) - to_integer(len));
    to_integer(old(len)) <= 15;
    0 <= to_integer(len);
   };
   have to_integer(len) <= to_integer(old(len)) by arithmetic() using {
    to_integer(len) == at(before_decrement, to_integer(len)) - 1;
    at(before_decrement, to_integer(len)) <= to_integer(old(len));
   };
   apply(uint64_to_integer_less_equal_implies_less_equal(len, old(len)));
   apply(uint64_subtract_to_integer(old(len), len));
   have to_integer(old(len) - at(before_decrement, len)) <= 14 by arithmetic() using {
    to_integer(old(len) - at(before_decrement, len)) == to_integer(old(len)) - at(before_decrement, to_integer(len));
    to_integer(old(len)) <= 15;
    to_integer(1u64) <= at(before_decrement, to_integer(len));
   };
   apply(uint64_to_integer_less_equal_implies_less_equal(old(len) - at(before_decrement, len), 14u64));
   have to_integer(old(len) - at(before_decrement, len)) + to_integer(1u64) <= 18446744073709551615 by arithmetic() using { to_integer(old(len) - at(before_decrement, len)) <= 14; };
   apply(uint64_add_to_integer(old(len) - at(before_decrement, len), 1u64));
   have to_integer(old(len) - len) == to_integer((old(len) - at(before_decrement, len)) + 1u64) by arithmetic() using {
    to_integer(old(len) - len) == to_integer(old(len)) - to_integer(len);
    to_integer(len) == at(before_decrement, to_integer(len)) - 1;
    to_integer(old(len) - at(before_decrement, len)) == to_integer(old(len)) - at(before_decrement, to_integer(len));
    to_integer((old(len) - at(before_decrement, len)) + 1u64) == to_integer(old(len) - at(before_decrement, len)) + to_integer(1u64);
   };
   apply(uint64_to_integer_equal_implies_equal(old(len) - len, (old(len) - at(before_decrement, len)) + 1u64));
   have buf == at(before_decrement, buf) + 1 by simp();
   have buf == old(buf) + (old(len) - len) by {
    rewrite(buf == at(before_decrement, buf) + 1);
    rewrite(old(len) - len == (old(len) - at(before_decrement, len)) + 1u64);
    arithmetic_certificate rules {
     premise 0: at(before_decrement, buf) == old(buf) + (old(len) - at(before_decrement, len)) => at(before_decrement, buf) == old(buf) + (old(len) - at(before_decrement, len));
     premise 1: old(len) - at(before_decrement, len) <= 14u64 => old(len) - at(before_decrement, len) <= 14u64;
     pointer_translation relation 0 bounds [1] => at(before_decrement, buf) + 1 == old(buf) + ((old(len) - at(before_decrement, len)) + 1u64);
     conclusion 0;
    }
   }
   have to_integer(len) == to_integer(at(before_decrement, len) - 1u64) by simp();
   apply(uint64_to_integer_equal_implies_equal(len, at(before_decrement, len) - 1u64));
   have len <= at(before_decrement, len) - 1u64 by simp();
   apply(uint64_to_integer_less_equal_implies_less_equal(len, 15u64));
   apply(uint64_less_equal_transitive(len, 15u64, 9223372036854775807u64));
   have viewable(buf[0u64..len]) by {
    transport(at(before_decrement, viewable(buf[0u64..len])), viewable(buf[0u64..len])) using {
     buf == at(before_decrement, buf) + 1;
     at(before_decrement, viewable(buf[0u64..len]));
     1u64 <= at(before_decrement, len);
     len <= at(before_decrement, len) - 1u64;
     len <= 15u64;
     len <= 9223372036854775807u64;
    };
   }
   have old(len) - len <= 15u64 by {
    have to_integer(old(len) - len) <= 15 by arithmetic() using {
     to_integer(old(len) - len) == to_integer(old(len)) - to_integer(len);
     to_integer(old(len)) <= 15;
     0 <= to_integer(len);
    };
    apply(uint64_to_integer_less_equal_implies_less_equal(old(len) - len, 15u64));
   }
   have old(len) - len <= 22208u64 by arithmetic() using { old(len) - len <= 15u64; };
   apply(zlib_prefix_observation(old(len), len));
   apply(zlib_prefix_observation(old(len), at(before_decrement, len)));
   have to_integer(zlib_prefix_count(old(len), len)) == to_integer(zlib_prefix_count(old(len), at(before_decrement, len))) + 1 by arithmetic() using {
    to_integer(zlib_prefix_count(old(len), len)) == to_integer(old(len) - len);
    to_integer(zlib_prefix_count(old(len), at(before_decrement, len))) == to_integer(old(len) - at(before_decrement, len));
    to_integer(old(len) - len) == to_integer(old(len)) - to_integer(len);
    to_integer(old(len) - at(before_decrement, len)) == to_integer(old(len)) - at(before_decrement, to_integer(len));
    to_integer(len) == at(before_decrement, to_integer(len)) - 1;
   };

   have 0 < to_integer(zlib_prefix_count(old(len), len)) by arithmetic() using {
    to_integer(zlib_prefix_count(old(len), len)) == to_integer(zlib_prefix_count(old(len), at(before_decrement, len))) + 1;
    to_integer(zlib_prefix_count(old(len), at(before_decrement, len))) == to_integer(old(len) - at(before_decrement, len));
    to_integer(old(len) - at(before_decrement, len)) == to_integer(old(len)) - at(before_decrement, to_integer(len));
    at(before_decrement, to_integer(len)) <= to_integer(old(len));
   };
   have to_integer(1) <= to_integer(zlib_prefix_count(old(len), len)) by arithmetic() using { 0 < to_integer(zlib_prefix_count(old(len), len)); };
   apply(int32_to_integer_less_equal_implies_less_equal(1, zlib_prefix_count(old(len), len)));
   apply(zlib_positive_count(zlib_prefix_count(old(len), len)));
   apply(int32_nonnegative_subtract_within_value_is_defined(zlib_prefix_count(old(len), len), 1));
   apply(int32_subtract_to_integer(zlib_prefix_count(old(len), len), 1));
   have to_integer(zlib_prefix_count(old(len), len) - 1) == to_integer(zlib_prefix_count(old(len), at(before_decrement, len))) by arithmetic() using {
    to_integer(zlib_prefix_count(old(len), len) - 1) == to_integer(zlib_prefix_count(old(len), len)) - to_integer(1);
    to_integer(zlib_prefix_count(old(len), len)) == to_integer(zlib_prefix_count(old(len), at(before_decrement, len))) + 1;
   };
   apply(int32_to_integer_equal_implies_equal(zlib_prefix_count(old(len), len) - 1, zlib_prefix_count(old(len), at(before_decrement, len))));
   apply(zlib_prefix_append(old(buf), old(len), len));
   apply(adler_weighted_prefix_step(old(buf), zlib_prefix_count(old(len), len)));
   have old(buf)[zlib_prefix_count(old(len), len) - 1] == at(before_add, __click_call_result0[0]) by simp() using {
    zlib_prefix_count(old(len), len) - 1 == zlib_prefix_count(old(len), at(before_decrement, len));
    at(before_add, __click_call_result0[0]) == old(buf)[zlib_prefix_count(old(len), at(before_decrement, len))];
   };
   have adler_byte_sum(old(buf), zlib_prefix_count(old(len), len) - 1) == adler_byte_sum(old(buf), zlib_prefix_count(old(len), at(before_decrement, len))) by simp() using {
    zlib_prefix_count(old(len), len) - 1 == zlib_prefix_count(old(len), at(before_decrement, len));
   };
   have adler_weighted_sum(old(buf), zlib_prefix_count(old(len), len) - 1, zlib_prefix_count(old(len), len) - 1) == adler_weighted_sum(old(buf), zlib_prefix_count(old(len), at(before_decrement, len)), zlib_prefix_count(old(len), at(before_decrement, len))) by simp() using {
    zlib_prefix_count(old(len), len) - 1 == zlib_prefix_count(old(len), at(before_decrement, len));
   };
   apply(zlib_equal_byte_integers(old(buf)[zlib_prefix_count(old(len), len) - 1], at(before_add, __click_call_result0[0])));
   have zlib_byte_integer(old(buf)[zlib_prefix_count(old(len), len) - 1]) == at(before_add, to_integer((int32)__click_call_result0[0])) by arithmetic() using {
    zlib_byte_integer(old(buf)[zlib_prefix_count(old(len), len) - 1]) == zlib_byte_integer(at(before_add, __click_call_result0[0]));
    at(before_add, zlib_byte_integer(__click_call_result0[0])) == at(before_add, to_integer((int32)__click_call_result0[0]));
   };
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), zlib_prefix_count(old(len), len)) by arithmetic() using {
    adler_byte_sum(old(buf), zlib_prefix_count(old(len), len)) == adler_byte_sum(old(buf), zlib_prefix_count(old(len), len) - 1) + zlib_byte_integer(old(buf)[zlib_prefix_count(old(len), len) - 1]);
    adler_byte_sum(old(buf), zlib_prefix_count(old(len), len) - 1) == adler_byte_sum(old(buf), zlib_prefix_count(old(len), at(before_decrement, len)));
    zlib_byte_integer(old(buf)[zlib_prefix_count(old(len), len) - 1]) == at(before_add, to_integer((int32)__click_call_result0[0]));
    to_integer(adler) == at(before_add, to_integer(adler)) + at(before_add, to_integer((int32)__click_call_result0[0]));
    at(before_add, to_integer(adler)) == 1 + adler_byte_sum(old(buf), zlib_prefix_count(old(len), at(before_decrement, len)));
   };
   have to_integer(sum2) == to_integer(zlib_prefix_count(old(len), len)) + adler_weighted_sum(old(buf), zlib_prefix_count(old(len), len), zlib_prefix_count(old(len), len)) by arithmetic() using {
    adler_weighted_sum(old(buf), zlib_prefix_count(old(len), len), zlib_prefix_count(old(len), len)) == adler_weighted_sum(old(buf), zlib_prefix_count(old(len), len) - 1, zlib_prefix_count(old(len), len) - 1) + adler_byte_sum(old(buf), zlib_prefix_count(old(len), len));
    adler_weighted_sum(old(buf), zlib_prefix_count(old(len), len) - 1, zlib_prefix_count(old(len), len) - 1) == adler_weighted_sum(old(buf), zlib_prefix_count(old(len), at(before_decrement, len)), zlib_prefix_count(old(len), at(before_decrement, len)));
    to_integer(sum2) == at(before_sum, to_integer(sum2)) + to_integer(adler);
    at(before_sum, to_integer(sum2)) == to_integer(zlib_prefix_count(old(len), at(before_decrement, len))) + adler_weighted_sum(old(buf), zlib_prefix_count(old(len), at(before_decrement, len)), zlib_prefix_count(old(len), at(before_decrement, len)));
    to_integer(adler) == 1 + adler_byte_sum(old(buf), zlib_prefix_count(old(len), len));
    to_integer(zlib_prefix_count(old(len), len)) == to_integer(zlib_prefix_count(old(len), at(before_decrement, len))) + 1;
   };
   close_invariants() by { simp(); }
   }
  }
 }
 apply(uint64_to_integer_less_equal_implies_less_equal(adler, 3826u64));
 apply(uint64_to_integer_less_equal_implies_less_equal(sum2, 57390u64));
 have adler < 65521u64 by arithmetic() using { adler <= 3826u64; };
 apply(uint64_less_than_implies_not_greater_equal(adler, 65521u64));
 execute_until(assignment(sum2, 4));
 apply(zlib_short_result(old(buf), old((int32)(uint32)len), adler, sum2));
 apply(uint64_remainder_to_integer(sum2, 65521u64));
 apply(integer_positive_divisor_remainder_upper(to_integer(sum2), 65521));
 mark before_reduction;
 step();
 have sum2 == at(before_reduction, sum2 % 65521u64) by simp();
 have to_integer(sum2) == at(before_reduction, to_integer(sum2 % 65521u64)) by simp() using { sum2 == at(before_reduction, sum2 % 65521u64); };
 have to_integer(sum2) <= 65520 by arithmetic() using {
  to_integer(sum2) == at(before_reduction, to_integer(sum2 % 65521u64));
  at(before_reduction, to_integer(sum2 % 65521u64)) == truncating_remainder(at(before_reduction, to_integer(sum2)), 65521);
  truncating_remainder(at(before_reduction, to_integer(sum2)), 65521) <= 65521 - 1;
 };
 apply(uint64_to_integer_less_equal_implies_less_equal(sum2, 65520u64));
 have adler <= 65535u64 by arithmetic() using { adler <= 3826u64; };
 have sum2 <= 65535u64 by arithmetic() using { sum2 <= 65520u64; };
 apply(uint64_pack_uint16_to_integer(adler, sum2));
 have to_integer(adler | (sum2 << 16)) <= to_integer(4294967295u64) by arithmetic() using {
  to_integer(adler | (sum2 << 16)) == to_integer(adler) + 65536 * to_integer(sum2);
  to_integer(adler) <= 3826;
  to_integer(sum2) <= 65520;
 };
 apply(uint64_to_integer_less_equal_implies_less_equal(adler | (sum2 << 16), 4294967295u64));
 execute(); simp();

  } else {
   have 16u64 <= len by arithmetic() using { not (len <= 15u64); len <= 2147483647u64; };

 have viewable(buf[0u64..len]) by simp();
 execute_until(loop(1));
 // Each outer head describes the reduced checksum of the completed prefix.
 loop {
  decreases to_integer(len);
  invariant len <= old(len);
  invariant old(len) <= 2147483647u64;
  invariant buf == old(buf) + (old(len) - len);
  invariant viewable(buf[0u64..len]);
  invariant adler <= 65520u64;
  invariant sum2 <= 65520u64;
  invariant to_integer(adler) == adler_spec_a(old(buf), zlib_prefix_count(old(len), len), 1);
  invariant to_integer(sum2) == adler_spec_b(old(buf), zlib_prefix_count(old(len), len), 1, 0);
  initialize by {
   have zlib_prefix_count(old(len), len) == 0 by { unfold(zlib_prefix_count(old(len), len)); simp(); }
   apply(zlib_batch_empty_components(old(buf)));
   have adler == 1u64 by simp();
   have sum2 == 0u64 by simp();
   have to_integer(adler) == 1 by simp() using { adler == 1u64; };
   have to_integer(sum2) == 0 by simp() using { sum2 == 0u64; };
   have adler_spec_a(old(buf), zlib_prefix_count(old(len), len), 1) == 1 by { rewrite(zlib_prefix_count(old(len), len) == 0); assumption(); }
   have adler_spec_b(old(buf), zlib_prefix_count(old(len), len), 1, 0) == 0 by { rewrite(zlib_prefix_count(old(len), len) == 0); assumption(); }
   have to_integer(adler) == adler_spec_a(old(buf), zlib_prefix_count(old(len), len), 1) by arithmetic() using {
    to_integer(adler) == 1;
    adler_spec_a(old(buf), zlib_prefix_count(old(len), len), 1) == 1;
   };
   have to_integer(sum2) == adler_spec_b(old(buf), zlib_prefix_count(old(len), len), 1, 0) by arithmetic() using {
    to_integer(sum2) == 0;
    adler_spec_b(old(buf), zlib_prefix_count(old(len), len), 1, 0) == 0;
   };
   simp();
  }
  preserve by {
   have 5552u64 <= len by assumption();
   have len <= 2147483647u64 by arithmetic() using { len <= old(len); old(len) <= 2147483647u64; };
   have len <= 9223372036854775807u64 by arithmetic() using { len <= 2147483647u64; };
   have viewable(buf[0u64..5552u64]) by simp();
   mark batch_entry;
   step(); step();
   execute_until(loop(2));
   loop {
    decreases to_integer(n);
    invariant 1u32 <= n;
    invariant n <= 347u32;
    invariant len == at(loop(2).entry, len);
    invariant len <= old(len) - 5552u64;
    invariant len <= 2147478095u64;
    invariant len <= old(len);
    invariant 5552u64 <= old(len) - len;
    invariant 5552u64 <= old(len);
    invariant old(len) <= 2147483647u64;
    invariant at(loop(2).entry, buf) == old(buf) + (old(len) - len - 5552u64);

    invariant at(loop(2).entry, len) <= 2147483647u64;
    invariant at(loop(2).entry, adler) <= 65520u64;
    invariant at(loop(2).entry, sum2) <= 65520u64;
    invariant buf == at(loop(2).entry, buf) + zlib_batch_count(n);
    invariant viewable(buf[0u64..16u64 * (uint64)n]);
    // Preserve the pending batch and every byte following it.
    invariant viewable(buf[0u64..16u64 * (uint64)n + len]);
    invariant to_integer(adler) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), zlib_batch_count(n));
    invariant to_integer(sum2) == to_integer(at(loop(2).entry, sum2)) + to_integer(zlib_batch_count(n)) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), zlib_batch_count(n), zlib_batch_count(n));
    invariant to_integer(adler) <= 65520 + 255 * to_integer(zlib_batch_count(n));
    invariant to_integer(sum2) <= 65520 + 1481280 * to_integer(zlib_batch_count(n));
    initialize by {
     have len <= 2147483647u64 by arithmetic() using {
      at(batch_entry, len) <= 2147483647u64;
      5552u64 <= at(batch_entry, len);
      len == at(batch_entry, len) - 5552u64;
     };
     have 5552u64 <= old(len) by arithmetic() using { 5552u64 <= at(batch_entry, len); at(batch_entry, len) <= old(len); };
     have len <= old(len) - 5552u64 by arithmetic() using {
      5552u64 <= at(batch_entry, len); at(batch_entry, len) <= old(len); old(len) <= 2147483647u64;
      len == at(batch_entry, len) - 5552u64;
     };
     have len <= old(len) by arithmetic() using { len <= old(len) - 5552u64; 5552u64 <= old(len); old(len) <= 2147483647u64; };
     have 5552u64 <= old(len) - len by arithmetic() using { len <= old(len); len <= old(len) - 5552u64; 5552u64 <= old(len); old(len) <= 2147483647u64; };
     have old(len) - len - 5552u64 == old(len) - at(batch_entry, len) by arithmetic() using {
      5552u64 <= at(batch_entry, len); at(batch_entry, len) <= old(len); old(len) <= 2147483647u64;
      len == at(batch_entry, len) - 5552u64;
     };
     have buf == old(buf) + (old(len) - len - 5552u64) by simp() using {
      buf == old(buf) + (old(len) - at(batch_entry, len));
      old(len) - len - 5552u64 == old(len) - at(batch_entry, len);
     };
     have len <= 2147478095u64 by arithmetic() using { len <= old(len) - 5552u64; 5552u64 <= old(len); old(len) <= 2147483647u64; };
     have n == 347u32 by simp();
     have len == at(loop(2).entry, len) by simp();
     have buf == at(loop(2).entry, buf) by simp();
     have adler == at(loop(2).entry, adler) by simp();
     have sum2 == at(loop(2).entry, sum2) by simp();
     have viewable(buf[0u64..5552u64]) by {
      transport(at(batch_entry, viewable(buf[0u64..5552u64])), viewable(buf[0u64..5552u64])) using {
       at(batch_entry, viewable(buf[0u64..5552u64]));
      };
     }
     have viewable(buf[0u64..16u64 * (uint64)n]) by assumption();
     have 16u64 * (uint64)n + len == at(batch_entry, len) by arithmetic() using {
      n == 347u32; len == at(batch_entry, len) - 5552u64;
      5552u64 <= at(batch_entry, len); at(batch_entry, len) <= 2147483647u64;
     };
     have 16u64 * (uint64)n + len <= at(batch_entry, len) by simp() using { 16u64 * (uint64)n + len == at(batch_entry, len); };
     have 16u64 * (uint64)n + len <= 9223372036854775807u64 by arithmetic() using {
      16u64 * (uint64)n + len == at(batch_entry, len);
      at(batch_entry, len) <= 2147483647u64;
      n == 347u32; len <= 2147478095u64;
     };
     have viewable(buf[0u64..16u64 * (uint64)n + len]) by {
      transport(at(batch_entry, viewable(buf[0u64..len])), viewable(buf[0u64..16u64 * (uint64)n + len])) using {
       at(batch_entry, viewable(buf[0u64..len]));
       buf == at(batch_entry, buf);
       16u64 * (uint64)n + len == at(batch_entry, len);
       16u64 * (uint64)n + len <= at(batch_entry, len);
       16u64 * (uint64)n + len <= 9223372036854775807u64;
       at(batch_entry, len) <= 9223372036854775807u64;
      };
     }
     apply(zlib_batch_prefix_initial());
     have zlib_batch_count(n) == 0 by assumption();
     apply(uint64_less_equal_to_integer(adler, 65520u64));
     apply(uint64_less_equal_to_integer(sum2, 65520u64));
     apply(adler_sum_empty(at(loop(2).entry, buf), 0));
     have buf == at(loop(2).entry, buf) + zlib_batch_count(n) by { rewrite(zlib_batch_count(n) == 0); assumption(); }
     have to_integer(adler) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), zlib_batch_count(n)) by {
      rewrite(zlib_batch_count(n) == 0); rewrite(adler_byte_sum(at(loop(2).entry, buf), 0) == 0); normalize();
     }
     have to_integer(sum2) == to_integer(at(loop(2).entry, sum2)) + to_integer(zlib_batch_count(n)) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), zlib_batch_count(n), zlib_batch_count(n)) by {
      rewrite(zlib_batch_count(n) == 0); rewrite(adler_weighted_sum(at(loop(2).entry, buf), 0, 0) == 0); normalize();
     }
     have to_integer(adler) <= 65520 + 255 * to_integer(zlib_batch_count(n)) by { rewrite(zlib_batch_count(n) == 0); arithmetic() using { to_integer(adler) <= 65520; }; }
     have to_integer(sum2) <= 65520 + 1481280 * to_integer(zlib_batch_count(n)) by { rewrite(zlib_batch_count(n) == 0); arithmetic() using { to_integer(sum2) <= 65520; }; }
     simp();
    }
    preserve by {
     apply(zlib_batch_prefix_limit(n));
     apply(zlib_batch_nonempty_prefix(n));
     apply(zlib_batch_remaining_limit(n));
     apply(zlib_batch_nonempty_remaining(n));
     have 16u64 <= 16u64 * (uint64)n by { unfold(zlib_batch_remaining(n)); assumption(); }
     have 16u64 * (uint64)n <= 5552u64 by { unfold(zlib_batch_remaining(n)); assumption(); }
     have 1u64 <= 16u64 * (uint64)n by arithmetic() using { 16u64 <= 16u64 * (uint64)n; };
     have 16u64 * (uint64)n <= 9223372036854775807u64 by arithmetic() using { 16u64 * (uint64)n <= 5552u64; };
     apply(zlib_batch_cursor(at(loop(2).entry, buf), n));
     have buf == at(loop(2).entry, buf) + (5552u64 - zlib_batch_remaining(n)) by simp() using {
      buf == at(loop(2).entry, buf) + zlib_batch_count(n);
      at(loop(2).entry, buf) + zlib_batch_count(n) == at(loop(2).entry, buf) + (5552u64 - zlib_batch_remaining(n));
     };
     have 5552u64 - zlib_batch_remaining(n) < 5552u64 by arithmetic() using { 16u64 <= zlib_batch_remaining(n); zlib_batch_remaining(n) <= 5552u64; };
     

     have len <= old(len) - 5552u64 by assumption();
     apply(zlib_full_stream_batch_read_bound(old(len), len, n));
     have old(len) - len - 5552u64 <= 2147483647u64 by arithmetic() using { len <= old(len); 5552u64 <= old(len) - len; old(len) <= 2147483647u64; };
     have 5552u64 - zlib_batch_remaining(n) <= 5552u64 by arithmetic() using { zlib_batch_remaining(n) <= 5552u64; };
     have (old(len) - len - 5552u64) + (5552u64 - zlib_batch_remaining(n)) <= 2147483647u64 by arithmetic() using {
      (old(len) - len - 5552u64) + (5552u64 - zlib_batch_remaining(n)) <= old(len) - 16u64;
      len <= old(len); 5552u64 <= old(len) - len; 5552u64 <= old(len); old(len) <= 2147483647u64;
      zlib_batch_remaining(n) <= 5552u64;
     };
     apply(zlib_full_native_cursor_join(old(buf), old(len) - len - 5552u64, 5552u64 - zlib_batch_remaining(n)));
     have buf == old(buf) + ((old(len) - len - 5552u64) + (5552u64 - zlib_batch_remaining(n))) by simp() using {
      buf == at(loop(2).entry, buf) + (5552u64 - zlib_batch_remaining(n));
      at(loop(2).entry, buf) == old(buf) + (old(len) - len - 5552u64);
      old(buf) + (old(len) - len - 5552u64) + (5552u64 - zlib_batch_remaining(n)) == old(buf) + ((old(len) - len - 5552u64) + (5552u64 - zlib_batch_remaining(n)));
     };
     have old(len) <= 9223372036854775807u64 by arithmetic() using { old(len) <= 2147483647u64; };
     mark before_block;
   execute_until(assignment(adler, 5));
   apply(zlib_batch_read_bound(n, 0u64));
   apply(zlib_full_stream_batch_lane_bound(old(len), len, n, 0u64));
   apply(zlib_batch_lane(n, 0));
   apply(zlib_batch_byte_lane(at(loop(2).entry, buf), n, 0));
   have buf[0] == at(loop(2).entry, buf)[zlib_batch_count(n)] by simp() using {
    buf == at(loop(2).entry, buf) + zlib_batch_count(n);
    (at(loop(2).entry, buf) + zlib_batch_count(n))[0] == at(loop(2).entry, buf)[zlib_batch_count(n) + 0];
   };
   apply(zlib_seeded_component_step(at(loop(2).entry, buf), zlib_batch_count(n), adler, sum2, buf[0], at(loop(2).entry, adler), at(loop(2).entry, sum2)));
   have viewable(buf[0u64..1u64]) by simp();
   mark byte_0;
   step();
   execute_until(assignment(sum2, 5));
   step();
   have adler == at(byte_0, adler + (uint64)(uint32)buf[0]) by simp();
   have sum2 == at(byte_0, sum2 + (adler + (uint64)(uint32)buf[0])) by simp();
   have to_integer(adler) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), zlib_batch_count(n) + 1) by simp() using {
    adler == at(byte_0, adler + (uint64)(uint32)buf[0]);
    at(byte_0, to_integer(adler + (uint64)(uint32)buf[0])) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), zlib_batch_count(n) + 1);
   };
   have to_integer(sum2) == to_integer(at(loop(2).entry, sum2)) + to_integer(zlib_batch_count(n) + 1) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), zlib_batch_count(n) + 1, zlib_batch_count(n) + 1) by simp() using {
    sum2 == at(byte_0, sum2 + (adler + (uint64)(uint32)buf[0]));
    at(byte_0, to_integer(sum2 + (adler + (uint64)(uint32)buf[0]))) == to_integer(at(loop(2).entry, sum2)) + to_integer(zlib_batch_count(n) + 1) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), zlib_batch_count(n) + 1, zlib_batch_count(n) + 1);
   };
   have to_integer(adler) <= 65520 + 255 * to_integer(zlib_batch_count(n) + 1) by simp() using {
    adler == at(byte_0, adler + (uint64)(uint32)buf[0]);
    at(byte_0, to_integer(adler + (uint64)(uint32)buf[0])) <= 65520 + 255 * to_integer(zlib_batch_count(n) + 1);
   };
   have to_integer(sum2) <= 65520 + 1481280 * to_integer(zlib_batch_count(n) + 1) by simp() using {
    sum2 == at(byte_0, sum2 + (adler + (uint64)(uint32)buf[0]));
    at(byte_0, to_integer(sum2 + (adler + (uint64)(uint32)buf[0]))) <= 65520 + 1481280 * to_integer(zlib_batch_count(n) + 1);
   };
   have to_integer(adler) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 1)) by simp();
   have to_integer(sum2) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 1)) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 1), (zlib_batch_count(n) + 1)) by simp();
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 1)) by simp();
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 1)) by simp();
   execute_until(assignment(adler, 6));
   apply(zlib_batch_read_bound(n, 1u64));
   apply(zlib_full_stream_batch_lane_bound(old(len), len, n, 1u64));
   apply(zlib_batch_lane(n, 1));
   apply(zlib_batch_byte_lane(at(loop(2).entry, buf), n, 1));
   have buf[1] == at(loop(2).entry, buf)[(zlib_batch_count(n) + 1)] by simp() using {
    buf == at(loop(2).entry, buf) + zlib_batch_count(n);
    (at(loop(2).entry, buf) + zlib_batch_count(n))[1] == at(loop(2).entry, buf)[zlib_batch_count(n) + 1];
   };
   apply(zlib_seeded_component_step(at(loop(2).entry, buf), (zlib_batch_count(n) + 1), adler, sum2, buf[1], at(loop(2).entry, adler), at(loop(2).entry, sum2)));
   mark byte_1;
   step();
   execute_until(assignment(sum2, 6));
   step();
   have adler == at(byte_1, adler + (uint64)(uint32)buf[1]) by simp();
   have sum2 == at(byte_1, sum2 + (adler + (uint64)(uint32)buf[1])) by simp();
   have to_integer(adler) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 1) + 1) by simp() using {
    adler == at(byte_1, adler + (uint64)(uint32)buf[1]);
    at(byte_1, to_integer(adler + (uint64)(uint32)buf[1])) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 1) + 1);
   };
   have to_integer(sum2) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 1) + 1) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 1) + 1, (zlib_batch_count(n) + 1) + 1) by simp() using {
    sum2 == at(byte_1, sum2 + (adler + (uint64)(uint32)buf[1]));
    at(byte_1, to_integer(sum2 + (adler + (uint64)(uint32)buf[1]))) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 1) + 1) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 1) + 1, (zlib_batch_count(n) + 1) + 1);
   };
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 1) + 1) by simp() using {
    adler == at(byte_1, adler + (uint64)(uint32)buf[1]);
    at(byte_1, to_integer(adler + (uint64)(uint32)buf[1])) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 1) + 1);
   };
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 1) + 1) by simp() using {
    sum2 == at(byte_1, sum2 + (adler + (uint64)(uint32)buf[1]));
    at(byte_1, to_integer(sum2 + (adler + (uint64)(uint32)buf[1]))) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 1) + 1);
   };
   have to_integer(adler) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 2)) by simp();
   have to_integer(sum2) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 2)) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 2), (zlib_batch_count(n) + 2)) by simp();
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 2)) by simp();
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 2)) by simp();
   execute_until(assignment(adler, 7));
   apply(zlib_batch_read_bound(n, 2u64));
   apply(zlib_full_stream_batch_lane_bound(old(len), len, n, 2u64));
   apply(zlib_batch_lane(n, 2));
   apply(zlib_batch_byte_lane(at(loop(2).entry, buf), n, 2));
   have buf[2] == at(loop(2).entry, buf)[(zlib_batch_count(n) + 2)] by simp() using {
    buf == at(loop(2).entry, buf) + zlib_batch_count(n);
    (at(loop(2).entry, buf) + zlib_batch_count(n))[2] == at(loop(2).entry, buf)[zlib_batch_count(n) + 2];
   };
   apply(zlib_seeded_component_step(at(loop(2).entry, buf), (zlib_batch_count(n) + 2), adler, sum2, buf[2], at(loop(2).entry, adler), at(loop(2).entry, sum2)));
   mark byte_2;
   step();
   execute_until(assignment(sum2, 7));
   step();
   have adler == at(byte_2, adler + (uint64)(uint32)buf[2]) by simp();
   have sum2 == at(byte_2, sum2 + (adler + (uint64)(uint32)buf[2])) by simp();
   have to_integer(adler) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 2) + 1) by simp() using {
    adler == at(byte_2, adler + (uint64)(uint32)buf[2]);
    at(byte_2, to_integer(adler + (uint64)(uint32)buf[2])) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 2) + 1);
   };
   have to_integer(sum2) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 2) + 1) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 2) + 1, (zlib_batch_count(n) + 2) + 1) by simp() using {
    sum2 == at(byte_2, sum2 + (adler + (uint64)(uint32)buf[2]));
    at(byte_2, to_integer(sum2 + (adler + (uint64)(uint32)buf[2]))) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 2) + 1) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 2) + 1, (zlib_batch_count(n) + 2) + 1);
   };
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 2) + 1) by simp() using {
    adler == at(byte_2, adler + (uint64)(uint32)buf[2]);
    at(byte_2, to_integer(adler + (uint64)(uint32)buf[2])) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 2) + 1);
   };
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 2) + 1) by simp() using {
    sum2 == at(byte_2, sum2 + (adler + (uint64)(uint32)buf[2]));
    at(byte_2, to_integer(sum2 + (adler + (uint64)(uint32)buf[2]))) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 2) + 1);
   };
   have to_integer(adler) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 3)) by simp();
   have to_integer(sum2) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 3)) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 3), (zlib_batch_count(n) + 3)) by simp();
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 3)) by simp();
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 3)) by simp();
   execute_until(assignment(adler, 8));
   apply(zlib_batch_read_bound(n, 3u64));
   apply(zlib_full_stream_batch_lane_bound(old(len), len, n, 3u64));
   apply(zlib_batch_lane(n, 3));
   apply(zlib_batch_byte_lane(at(loop(2).entry, buf), n, 3));
   have buf[3] == at(loop(2).entry, buf)[(zlib_batch_count(n) + 3)] by simp() using {
    buf == at(loop(2).entry, buf) + zlib_batch_count(n);
    (at(loop(2).entry, buf) + zlib_batch_count(n))[3] == at(loop(2).entry, buf)[zlib_batch_count(n) + 3];
   };
   apply(zlib_seeded_component_step(at(loop(2).entry, buf), (zlib_batch_count(n) + 3), adler, sum2, buf[3], at(loop(2).entry, adler), at(loop(2).entry, sum2)));
   mark byte_3;
   step();
   execute_until(assignment(sum2, 8));
   step();
   have adler == at(byte_3, adler + (uint64)(uint32)buf[3]) by simp();
   have sum2 == at(byte_3, sum2 + (adler + (uint64)(uint32)buf[3])) by simp();
   have to_integer(adler) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 3) + 1) by simp() using {
    adler == at(byte_3, adler + (uint64)(uint32)buf[3]);
    at(byte_3, to_integer(adler + (uint64)(uint32)buf[3])) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 3) + 1);
   };
   have to_integer(sum2) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 3) + 1) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 3) + 1, (zlib_batch_count(n) + 3) + 1) by simp() using {
    sum2 == at(byte_3, sum2 + (adler + (uint64)(uint32)buf[3]));
    at(byte_3, to_integer(sum2 + (adler + (uint64)(uint32)buf[3]))) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 3) + 1) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 3) + 1, (zlib_batch_count(n) + 3) + 1);
   };
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 3) + 1) by simp() using {
    adler == at(byte_3, adler + (uint64)(uint32)buf[3]);
    at(byte_3, to_integer(adler + (uint64)(uint32)buf[3])) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 3) + 1);
   };
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 3) + 1) by simp() using {
    sum2 == at(byte_3, sum2 + (adler + (uint64)(uint32)buf[3]));
    at(byte_3, to_integer(sum2 + (adler + (uint64)(uint32)buf[3]))) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 3) + 1);
   };
   have to_integer(adler) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 4)) by simp();
   have to_integer(sum2) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 4)) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 4), (zlib_batch_count(n) + 4)) by simp();
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 4)) by simp();
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 4)) by simp();
   execute_until(assignment(adler, 9));
   apply(zlib_batch_read_bound(n, 4u64));
   apply(zlib_full_stream_batch_lane_bound(old(len), len, n, 4u64));
   apply(zlib_batch_lane(n, 4));
   apply(zlib_batch_byte_lane(at(loop(2).entry, buf), n, 4));
   have buf[4] == at(loop(2).entry, buf)[(zlib_batch_count(n) + 4)] by simp() using {
    buf == at(loop(2).entry, buf) + zlib_batch_count(n);
    (at(loop(2).entry, buf) + zlib_batch_count(n))[4] == at(loop(2).entry, buf)[zlib_batch_count(n) + 4];
   };
   apply(zlib_seeded_component_step(at(loop(2).entry, buf), (zlib_batch_count(n) + 4), adler, sum2, buf[4], at(loop(2).entry, adler), at(loop(2).entry, sum2)));
   mark byte_4;
   step();
   execute_until(assignment(sum2, 9));
   step();
   have adler == at(byte_4, adler + (uint64)(uint32)buf[4]) by simp();
   have sum2 == at(byte_4, sum2 + (adler + (uint64)(uint32)buf[4])) by simp();
   have to_integer(adler) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 4) + 1) by simp() using {
    adler == at(byte_4, adler + (uint64)(uint32)buf[4]);
    at(byte_4, to_integer(adler + (uint64)(uint32)buf[4])) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 4) + 1);
   };
   have to_integer(sum2) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 4) + 1) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 4) + 1, (zlib_batch_count(n) + 4) + 1) by simp() using {
    sum2 == at(byte_4, sum2 + (adler + (uint64)(uint32)buf[4]));
    at(byte_4, to_integer(sum2 + (adler + (uint64)(uint32)buf[4]))) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 4) + 1) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 4) + 1, (zlib_batch_count(n) + 4) + 1);
   };
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 4) + 1) by simp() using {
    adler == at(byte_4, adler + (uint64)(uint32)buf[4]);
    at(byte_4, to_integer(adler + (uint64)(uint32)buf[4])) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 4) + 1);
   };
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 4) + 1) by simp() using {
    sum2 == at(byte_4, sum2 + (adler + (uint64)(uint32)buf[4]));
    at(byte_4, to_integer(sum2 + (adler + (uint64)(uint32)buf[4]))) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 4) + 1);
   };
   have to_integer(adler) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 5)) by simp();
   have to_integer(sum2) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 5)) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 5), (zlib_batch_count(n) + 5)) by simp();
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 5)) by simp();
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 5)) by simp();
   execute_until(assignment(adler, 10));
   apply(zlib_batch_read_bound(n, 5u64));
   apply(zlib_full_stream_batch_lane_bound(old(len), len, n, 5u64));
   apply(zlib_batch_lane(n, 5));
   apply(zlib_batch_byte_lane(at(loop(2).entry, buf), n, 5));
   have buf[5] == at(loop(2).entry, buf)[(zlib_batch_count(n) + 5)] by simp() using {
    buf == at(loop(2).entry, buf) + zlib_batch_count(n);
    (at(loop(2).entry, buf) + zlib_batch_count(n))[5] == at(loop(2).entry, buf)[zlib_batch_count(n) + 5];
   };
   apply(zlib_seeded_component_step(at(loop(2).entry, buf), (zlib_batch_count(n) + 5), adler, sum2, buf[5], at(loop(2).entry, adler), at(loop(2).entry, sum2)));
   mark byte_5;
   step();
   execute_until(assignment(sum2, 10));
   step();
   have adler == at(byte_5, adler + (uint64)(uint32)buf[5]) by simp();
   have sum2 == at(byte_5, sum2 + (adler + (uint64)(uint32)buf[5])) by simp();
   have to_integer(adler) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 5) + 1) by simp() using {
    adler == at(byte_5, adler + (uint64)(uint32)buf[5]);
    at(byte_5, to_integer(adler + (uint64)(uint32)buf[5])) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 5) + 1);
   };
   have to_integer(sum2) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 5) + 1) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 5) + 1, (zlib_batch_count(n) + 5) + 1) by simp() using {
    sum2 == at(byte_5, sum2 + (adler + (uint64)(uint32)buf[5]));
    at(byte_5, to_integer(sum2 + (adler + (uint64)(uint32)buf[5]))) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 5) + 1) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 5) + 1, (zlib_batch_count(n) + 5) + 1);
   };
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 5) + 1) by simp() using {
    adler == at(byte_5, adler + (uint64)(uint32)buf[5]);
    at(byte_5, to_integer(adler + (uint64)(uint32)buf[5])) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 5) + 1);
   };
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 5) + 1) by simp() using {
    sum2 == at(byte_5, sum2 + (adler + (uint64)(uint32)buf[5]));
    at(byte_5, to_integer(sum2 + (adler + (uint64)(uint32)buf[5]))) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 5) + 1);
   };
   have to_integer(adler) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 6)) by simp();
   have to_integer(sum2) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 6)) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 6), (zlib_batch_count(n) + 6)) by simp();
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 6)) by simp();
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 6)) by simp();
   execute_until(assignment(adler, 11));
   apply(zlib_batch_read_bound(n, 6u64));
   apply(zlib_full_stream_batch_lane_bound(old(len), len, n, 6u64));
   apply(zlib_batch_lane(n, 6));
   apply(zlib_batch_byte_lane(at(loop(2).entry, buf), n, 6));
   have buf[6] == at(loop(2).entry, buf)[(zlib_batch_count(n) + 6)] by simp() using {
    buf == at(loop(2).entry, buf) + zlib_batch_count(n);
    (at(loop(2).entry, buf) + zlib_batch_count(n))[6] == at(loop(2).entry, buf)[zlib_batch_count(n) + 6];
   };
   apply(zlib_seeded_component_step(at(loop(2).entry, buf), (zlib_batch_count(n) + 6), adler, sum2, buf[6], at(loop(2).entry, adler), at(loop(2).entry, sum2)));
   mark byte_6;
   step();
   execute_until(assignment(sum2, 11));
   step();
   have adler == at(byte_6, adler + (uint64)(uint32)buf[6]) by simp();
   have sum2 == at(byte_6, sum2 + (adler + (uint64)(uint32)buf[6])) by simp();
   have to_integer(adler) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 6) + 1) by simp() using {
    adler == at(byte_6, adler + (uint64)(uint32)buf[6]);
    at(byte_6, to_integer(adler + (uint64)(uint32)buf[6])) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 6) + 1);
   };
   have to_integer(sum2) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 6) + 1) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 6) + 1, (zlib_batch_count(n) + 6) + 1) by simp() using {
    sum2 == at(byte_6, sum2 + (adler + (uint64)(uint32)buf[6]));
    at(byte_6, to_integer(sum2 + (adler + (uint64)(uint32)buf[6]))) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 6) + 1) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 6) + 1, (zlib_batch_count(n) + 6) + 1);
   };
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 6) + 1) by simp() using {
    adler == at(byte_6, adler + (uint64)(uint32)buf[6]);
    at(byte_6, to_integer(adler + (uint64)(uint32)buf[6])) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 6) + 1);
   };
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 6) + 1) by simp() using {
    sum2 == at(byte_6, sum2 + (adler + (uint64)(uint32)buf[6]));
    at(byte_6, to_integer(sum2 + (adler + (uint64)(uint32)buf[6]))) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 6) + 1);
   };
   have to_integer(adler) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 7)) by simp();
   have to_integer(sum2) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 7)) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 7), (zlib_batch_count(n) + 7)) by simp();
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 7)) by simp();
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 7)) by simp();
   execute_until(assignment(adler, 12));
   apply(zlib_batch_read_bound(n, 7u64));
   apply(zlib_full_stream_batch_lane_bound(old(len), len, n, 7u64));
   apply(zlib_batch_lane(n, 7));
   apply(zlib_batch_byte_lane(at(loop(2).entry, buf), n, 7));
   have buf[7] == at(loop(2).entry, buf)[(zlib_batch_count(n) + 7)] by simp() using {
    buf == at(loop(2).entry, buf) + zlib_batch_count(n);
    (at(loop(2).entry, buf) + zlib_batch_count(n))[7] == at(loop(2).entry, buf)[zlib_batch_count(n) + 7];
   };
   apply(zlib_seeded_component_step(at(loop(2).entry, buf), (zlib_batch_count(n) + 7), adler, sum2, buf[7], at(loop(2).entry, adler), at(loop(2).entry, sum2)));
   mark byte_7;
   step();
   execute_until(assignment(sum2, 12));
   step();
   have adler == at(byte_7, adler + (uint64)(uint32)buf[7]) by simp();
   have sum2 == at(byte_7, sum2 + (adler + (uint64)(uint32)buf[7])) by simp();
   have to_integer(adler) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 7) + 1) by simp() using {
    adler == at(byte_7, adler + (uint64)(uint32)buf[7]);
    at(byte_7, to_integer(adler + (uint64)(uint32)buf[7])) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 7) + 1);
   };
   have to_integer(sum2) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 7) + 1) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 7) + 1, (zlib_batch_count(n) + 7) + 1) by simp() using {
    sum2 == at(byte_7, sum2 + (adler + (uint64)(uint32)buf[7]));
    at(byte_7, to_integer(sum2 + (adler + (uint64)(uint32)buf[7]))) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 7) + 1) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 7) + 1, (zlib_batch_count(n) + 7) + 1);
   };
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 7) + 1) by simp() using {
    adler == at(byte_7, adler + (uint64)(uint32)buf[7]);
    at(byte_7, to_integer(adler + (uint64)(uint32)buf[7])) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 7) + 1);
   };
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 7) + 1) by simp() using {
    sum2 == at(byte_7, sum2 + (adler + (uint64)(uint32)buf[7]));
    at(byte_7, to_integer(sum2 + (adler + (uint64)(uint32)buf[7]))) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 7) + 1);
   };
   have to_integer(adler) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 8)) by simp();
   have to_integer(sum2) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 8)) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 8), (zlib_batch_count(n) + 8)) by simp();
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 8)) by simp();
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 8)) by simp();
   execute_until(assignment(adler, 13));
   apply(zlib_batch_read_bound(n, 8u64));
   apply(zlib_full_stream_batch_lane_bound(old(len), len, n, 8u64));
   apply(zlib_batch_lane(n, 8));
   apply(zlib_batch_byte_lane(at(loop(2).entry, buf), n, 8));
   have buf[8] == at(loop(2).entry, buf)[(zlib_batch_count(n) + 8)] by simp() using {
    buf == at(loop(2).entry, buf) + zlib_batch_count(n);
    (at(loop(2).entry, buf) + zlib_batch_count(n))[8] == at(loop(2).entry, buf)[zlib_batch_count(n) + 8];
   };
   apply(zlib_seeded_component_step(at(loop(2).entry, buf), (zlib_batch_count(n) + 8), adler, sum2, buf[8], at(loop(2).entry, adler), at(loop(2).entry, sum2)));
   mark byte_8;
   step();
   execute_until(assignment(sum2, 13));
   step();
   have adler == at(byte_8, adler + (uint64)(uint32)buf[8]) by simp();
   have sum2 == at(byte_8, sum2 + (adler + (uint64)(uint32)buf[8])) by simp();
   have to_integer(adler) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 8) + 1) by simp() using {
    adler == at(byte_8, adler + (uint64)(uint32)buf[8]);
    at(byte_8, to_integer(adler + (uint64)(uint32)buf[8])) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 8) + 1);
   };
   have to_integer(sum2) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 8) + 1) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 8) + 1, (zlib_batch_count(n) + 8) + 1) by simp() using {
    sum2 == at(byte_8, sum2 + (adler + (uint64)(uint32)buf[8]));
    at(byte_8, to_integer(sum2 + (adler + (uint64)(uint32)buf[8]))) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 8) + 1) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 8) + 1, (zlib_batch_count(n) + 8) + 1);
   };
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 8) + 1) by simp() using {
    adler == at(byte_8, adler + (uint64)(uint32)buf[8]);
    at(byte_8, to_integer(adler + (uint64)(uint32)buf[8])) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 8) + 1);
   };
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 8) + 1) by simp() using {
    sum2 == at(byte_8, sum2 + (adler + (uint64)(uint32)buf[8]));
    at(byte_8, to_integer(sum2 + (adler + (uint64)(uint32)buf[8]))) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 8) + 1);
   };
   have to_integer(adler) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 9)) by simp();
   have to_integer(sum2) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 9)) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 9), (zlib_batch_count(n) + 9)) by simp();
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 9)) by simp();
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 9)) by simp();
   execute_until(assignment(adler, 14));
   apply(zlib_batch_read_bound(n, 9u64));
   apply(zlib_full_stream_batch_lane_bound(old(len), len, n, 9u64));
   apply(zlib_batch_lane(n, 9));
   apply(zlib_batch_byte_lane(at(loop(2).entry, buf), n, 9));
   have buf[9] == at(loop(2).entry, buf)[(zlib_batch_count(n) + 9)] by simp() using {
    buf == at(loop(2).entry, buf) + zlib_batch_count(n);
    (at(loop(2).entry, buf) + zlib_batch_count(n))[9] == at(loop(2).entry, buf)[zlib_batch_count(n) + 9];
   };
   apply(zlib_seeded_component_step(at(loop(2).entry, buf), (zlib_batch_count(n) + 9), adler, sum2, buf[9], at(loop(2).entry, adler), at(loop(2).entry, sum2)));
   mark byte_9;
   step();
   execute_until(assignment(sum2, 14));
   step();
   have adler == at(byte_9, adler + (uint64)(uint32)buf[9]) by simp();
   have sum2 == at(byte_9, sum2 + (adler + (uint64)(uint32)buf[9])) by simp();
   have to_integer(adler) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 9) + 1) by simp() using {
    adler == at(byte_9, adler + (uint64)(uint32)buf[9]);
    at(byte_9, to_integer(adler + (uint64)(uint32)buf[9])) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 9) + 1);
   };
   have to_integer(sum2) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 9) + 1) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 9) + 1, (zlib_batch_count(n) + 9) + 1) by simp() using {
    sum2 == at(byte_9, sum2 + (adler + (uint64)(uint32)buf[9]));
    at(byte_9, to_integer(sum2 + (adler + (uint64)(uint32)buf[9]))) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 9) + 1) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 9) + 1, (zlib_batch_count(n) + 9) + 1);
   };
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 9) + 1) by simp() using {
    adler == at(byte_9, adler + (uint64)(uint32)buf[9]);
    at(byte_9, to_integer(adler + (uint64)(uint32)buf[9])) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 9) + 1);
   };
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 9) + 1) by simp() using {
    sum2 == at(byte_9, sum2 + (adler + (uint64)(uint32)buf[9]));
    at(byte_9, to_integer(sum2 + (adler + (uint64)(uint32)buf[9]))) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 9) + 1);
   };
   have to_integer(adler) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 10)) by simp();
   have to_integer(sum2) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 10)) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 10), (zlib_batch_count(n) + 10)) by simp();
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 10)) by simp();
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 10)) by simp();
   execute_until(assignment(adler, 15));
   apply(zlib_batch_read_bound(n, 10u64));
   apply(zlib_full_stream_batch_lane_bound(old(len), len, n, 10u64));
   apply(zlib_batch_lane(n, 10));
   apply(zlib_batch_byte_lane(at(loop(2).entry, buf), n, 10));
   have buf[10] == at(loop(2).entry, buf)[(zlib_batch_count(n) + 10)] by simp() using {
    buf == at(loop(2).entry, buf) + zlib_batch_count(n);
    (at(loop(2).entry, buf) + zlib_batch_count(n))[10] == at(loop(2).entry, buf)[zlib_batch_count(n) + 10];
   };
   apply(zlib_seeded_component_step(at(loop(2).entry, buf), (zlib_batch_count(n) + 10), adler, sum2, buf[10], at(loop(2).entry, adler), at(loop(2).entry, sum2)));
   mark byte_10;
   step();
   execute_until(assignment(sum2, 15));
   step();
   have adler == at(byte_10, adler + (uint64)(uint32)buf[10]) by simp();
   have sum2 == at(byte_10, sum2 + (adler + (uint64)(uint32)buf[10])) by simp();
   have to_integer(adler) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 10) + 1) by simp() using {
    adler == at(byte_10, adler + (uint64)(uint32)buf[10]);
    at(byte_10, to_integer(adler + (uint64)(uint32)buf[10])) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 10) + 1);
   };
   have to_integer(sum2) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 10) + 1) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 10) + 1, (zlib_batch_count(n) + 10) + 1) by simp() using {
    sum2 == at(byte_10, sum2 + (adler + (uint64)(uint32)buf[10]));
    at(byte_10, to_integer(sum2 + (adler + (uint64)(uint32)buf[10]))) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 10) + 1) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 10) + 1, (zlib_batch_count(n) + 10) + 1);
   };
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 10) + 1) by simp() using {
    adler == at(byte_10, adler + (uint64)(uint32)buf[10]);
    at(byte_10, to_integer(adler + (uint64)(uint32)buf[10])) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 10) + 1);
   };
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 10) + 1) by simp() using {
    sum2 == at(byte_10, sum2 + (adler + (uint64)(uint32)buf[10]));
    at(byte_10, to_integer(sum2 + (adler + (uint64)(uint32)buf[10]))) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 10) + 1);
   };
   have to_integer(adler) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 11)) by simp();
   have to_integer(sum2) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 11)) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 11), (zlib_batch_count(n) + 11)) by simp();
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 11)) by simp();
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 11)) by simp();
   execute_until(assignment(adler, 16));
   apply(zlib_batch_read_bound(n, 11u64));
   apply(zlib_full_stream_batch_lane_bound(old(len), len, n, 11u64));
   apply(zlib_batch_lane(n, 11));
   apply(zlib_batch_byte_lane(at(loop(2).entry, buf), n, 11));
   have buf[11] == at(loop(2).entry, buf)[(zlib_batch_count(n) + 11)] by simp() using {
    buf == at(loop(2).entry, buf) + zlib_batch_count(n);
    (at(loop(2).entry, buf) + zlib_batch_count(n))[11] == at(loop(2).entry, buf)[zlib_batch_count(n) + 11];
   };
   apply(zlib_seeded_component_step(at(loop(2).entry, buf), (zlib_batch_count(n) + 11), adler, sum2, buf[11], at(loop(2).entry, adler), at(loop(2).entry, sum2)));
   mark byte_11;
   step();
   execute_until(assignment(sum2, 16));
   step();
   have adler == at(byte_11, adler + (uint64)(uint32)buf[11]) by simp();
   have sum2 == at(byte_11, sum2 + (adler + (uint64)(uint32)buf[11])) by simp();
   have to_integer(adler) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 11) + 1) by simp() using {
    adler == at(byte_11, adler + (uint64)(uint32)buf[11]);
    at(byte_11, to_integer(adler + (uint64)(uint32)buf[11])) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 11) + 1);
   };
   have to_integer(sum2) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 11) + 1) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 11) + 1, (zlib_batch_count(n) + 11) + 1) by simp() using {
    sum2 == at(byte_11, sum2 + (adler + (uint64)(uint32)buf[11]));
    at(byte_11, to_integer(sum2 + (adler + (uint64)(uint32)buf[11]))) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 11) + 1) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 11) + 1, (zlib_batch_count(n) + 11) + 1);
   };
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 11) + 1) by simp() using {
    adler == at(byte_11, adler + (uint64)(uint32)buf[11]);
    at(byte_11, to_integer(adler + (uint64)(uint32)buf[11])) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 11) + 1);
   };
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 11) + 1) by simp() using {
    sum2 == at(byte_11, sum2 + (adler + (uint64)(uint32)buf[11]));
    at(byte_11, to_integer(sum2 + (adler + (uint64)(uint32)buf[11]))) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 11) + 1);
   };
   have to_integer(adler) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 12)) by simp();
   have to_integer(sum2) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 12)) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 12), (zlib_batch_count(n) + 12)) by simp();
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 12)) by simp();
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 12)) by simp();
   execute_until(assignment(adler, 17));
   apply(zlib_batch_read_bound(n, 12u64));
   apply(zlib_full_stream_batch_lane_bound(old(len), len, n, 12u64));
   apply(zlib_batch_lane(n, 12));
   apply(zlib_batch_byte_lane(at(loop(2).entry, buf), n, 12));
   have buf[12] == at(loop(2).entry, buf)[(zlib_batch_count(n) + 12)] by simp() using {
    buf == at(loop(2).entry, buf) + zlib_batch_count(n);
    (at(loop(2).entry, buf) + zlib_batch_count(n))[12] == at(loop(2).entry, buf)[zlib_batch_count(n) + 12];
   };
   apply(zlib_seeded_component_step(at(loop(2).entry, buf), (zlib_batch_count(n) + 12), adler, sum2, buf[12], at(loop(2).entry, adler), at(loop(2).entry, sum2)));
   mark byte_12;
   step();
   execute_until(assignment(sum2, 17));
   step();
   have adler == at(byte_12, adler + (uint64)(uint32)buf[12]) by simp();
   have sum2 == at(byte_12, sum2 + (adler + (uint64)(uint32)buf[12])) by simp();
   have to_integer(adler) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 12) + 1) by simp() using {
    adler == at(byte_12, adler + (uint64)(uint32)buf[12]);
    at(byte_12, to_integer(adler + (uint64)(uint32)buf[12])) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 12) + 1);
   };
   have to_integer(sum2) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 12) + 1) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 12) + 1, (zlib_batch_count(n) + 12) + 1) by simp() using {
    sum2 == at(byte_12, sum2 + (adler + (uint64)(uint32)buf[12]));
    at(byte_12, to_integer(sum2 + (adler + (uint64)(uint32)buf[12]))) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 12) + 1) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 12) + 1, (zlib_batch_count(n) + 12) + 1);
   };
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 12) + 1) by simp() using {
    adler == at(byte_12, adler + (uint64)(uint32)buf[12]);
    at(byte_12, to_integer(adler + (uint64)(uint32)buf[12])) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 12) + 1);
   };
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 12) + 1) by simp() using {
    sum2 == at(byte_12, sum2 + (adler + (uint64)(uint32)buf[12]));
    at(byte_12, to_integer(sum2 + (adler + (uint64)(uint32)buf[12]))) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 12) + 1);
   };
   have to_integer(adler) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 13)) by simp();
   have to_integer(sum2) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 13)) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 13), (zlib_batch_count(n) + 13)) by simp();
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 13)) by simp();
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 13)) by simp();
   execute_until(assignment(adler, 18));
   apply(zlib_batch_read_bound(n, 13u64));
   apply(zlib_full_stream_batch_lane_bound(old(len), len, n, 13u64));
   apply(zlib_batch_lane(n, 13));
   apply(zlib_batch_byte_lane(at(loop(2).entry, buf), n, 13));
   have buf[13] == at(loop(2).entry, buf)[(zlib_batch_count(n) + 13)] by simp() using {
    buf == at(loop(2).entry, buf) + zlib_batch_count(n);
    (at(loop(2).entry, buf) + zlib_batch_count(n))[13] == at(loop(2).entry, buf)[zlib_batch_count(n) + 13];
   };
   apply(zlib_seeded_component_step(at(loop(2).entry, buf), (zlib_batch_count(n) + 13), adler, sum2, buf[13], at(loop(2).entry, adler), at(loop(2).entry, sum2)));
   mark byte_13;
   step();
   execute_until(assignment(sum2, 18));
   step();
   have adler == at(byte_13, adler + (uint64)(uint32)buf[13]) by simp();
   have sum2 == at(byte_13, sum2 + (adler + (uint64)(uint32)buf[13])) by simp();
   have to_integer(adler) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 13) + 1) by simp() using {
    adler == at(byte_13, adler + (uint64)(uint32)buf[13]);
    at(byte_13, to_integer(adler + (uint64)(uint32)buf[13])) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 13) + 1);
   };
   have to_integer(sum2) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 13) + 1) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 13) + 1, (zlib_batch_count(n) + 13) + 1) by simp() using {
    sum2 == at(byte_13, sum2 + (adler + (uint64)(uint32)buf[13]));
    at(byte_13, to_integer(sum2 + (adler + (uint64)(uint32)buf[13]))) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 13) + 1) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 13) + 1, (zlib_batch_count(n) + 13) + 1);
   };
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 13) + 1) by simp() using {
    adler == at(byte_13, adler + (uint64)(uint32)buf[13]);
    at(byte_13, to_integer(adler + (uint64)(uint32)buf[13])) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 13) + 1);
   };
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 13) + 1) by simp() using {
    sum2 == at(byte_13, sum2 + (adler + (uint64)(uint32)buf[13]));
    at(byte_13, to_integer(sum2 + (adler + (uint64)(uint32)buf[13]))) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 13) + 1);
   };
   have to_integer(adler) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 14)) by simp();
   have to_integer(sum2) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 14)) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 14), (zlib_batch_count(n) + 14)) by simp();
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 14)) by simp();
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 14)) by simp();
   execute_until(assignment(adler, 19));
   apply(zlib_batch_read_bound(n, 14u64));
   apply(zlib_full_stream_batch_lane_bound(old(len), len, n, 14u64));
   apply(zlib_batch_lane(n, 14));
   apply(zlib_batch_byte_lane(at(loop(2).entry, buf), n, 14));
   have buf[14] == at(loop(2).entry, buf)[(zlib_batch_count(n) + 14)] by simp() using {
    buf == at(loop(2).entry, buf) + zlib_batch_count(n);
    (at(loop(2).entry, buf) + zlib_batch_count(n))[14] == at(loop(2).entry, buf)[zlib_batch_count(n) + 14];
   };
   apply(zlib_seeded_component_step(at(loop(2).entry, buf), (zlib_batch_count(n) + 14), adler, sum2, buf[14], at(loop(2).entry, adler), at(loop(2).entry, sum2)));
   mark byte_14;
   step();
   execute_until(assignment(sum2, 19));
   step();
   have adler == at(byte_14, adler + (uint64)(uint32)buf[14]) by simp();
   have sum2 == at(byte_14, sum2 + (adler + (uint64)(uint32)buf[14])) by simp();
   have to_integer(adler) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 14) + 1) by simp() using {
    adler == at(byte_14, adler + (uint64)(uint32)buf[14]);
    at(byte_14, to_integer(adler + (uint64)(uint32)buf[14])) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 14) + 1);
   };
   have to_integer(sum2) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 14) + 1) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 14) + 1, (zlib_batch_count(n) + 14) + 1) by simp() using {
    sum2 == at(byte_14, sum2 + (adler + (uint64)(uint32)buf[14]));
    at(byte_14, to_integer(sum2 + (adler + (uint64)(uint32)buf[14]))) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 14) + 1) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 14) + 1, (zlib_batch_count(n) + 14) + 1);
   };
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 14) + 1) by simp() using {
    adler == at(byte_14, adler + (uint64)(uint32)buf[14]);
    at(byte_14, to_integer(adler + (uint64)(uint32)buf[14])) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 14) + 1);
   };
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 14) + 1) by simp() using {
    sum2 == at(byte_14, sum2 + (adler + (uint64)(uint32)buf[14]));
    at(byte_14, to_integer(sum2 + (adler + (uint64)(uint32)buf[14]))) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 14) + 1);
   };
   have to_integer(adler) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 15)) by simp();
   have to_integer(sum2) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 15)) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 15), (zlib_batch_count(n) + 15)) by simp();
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 15)) by simp();
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 15)) by simp();
   execute_until(assignment(adler, 20));
   apply(zlib_batch_read_bound(n, 15u64));
   apply(zlib_full_stream_batch_lane_bound(old(len), len, n, 15u64));
   apply(zlib_batch_lane(n, 15));
   apply(zlib_batch_byte_lane(at(loop(2).entry, buf), n, 15));
   have buf[15] == at(loop(2).entry, buf)[(zlib_batch_count(n) + 15)] by simp() using {
    buf == at(loop(2).entry, buf) + zlib_batch_count(n);
    (at(loop(2).entry, buf) + zlib_batch_count(n))[15] == at(loop(2).entry, buf)[zlib_batch_count(n) + 15];
   };
   apply(zlib_seeded_component_step(at(loop(2).entry, buf), (zlib_batch_count(n) + 15), adler, sum2, buf[15], at(loop(2).entry, adler), at(loop(2).entry, sum2)));
   mark byte_15;
   step();
   execute_until(assignment(sum2, 20));
   step();
   have adler == at(byte_15, adler + (uint64)(uint32)buf[15]) by simp();
   have sum2 == at(byte_15, sum2 + (adler + (uint64)(uint32)buf[15])) by simp();
   have to_integer(adler) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 15) + 1) by simp() using {
    adler == at(byte_15, adler + (uint64)(uint32)buf[15]);
    at(byte_15, to_integer(adler + (uint64)(uint32)buf[15])) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 15) + 1);
   };
   have to_integer(sum2) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 15) + 1) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 15) + 1, (zlib_batch_count(n) + 15) + 1) by simp() using {
    sum2 == at(byte_15, sum2 + (adler + (uint64)(uint32)buf[15]));
    at(byte_15, to_integer(sum2 + (adler + (uint64)(uint32)buf[15]))) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 15) + 1) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 15) + 1, (zlib_batch_count(n) + 15) + 1);
   };
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 15) + 1) by simp() using {
    adler == at(byte_15, adler + (uint64)(uint32)buf[15]);
    at(byte_15, to_integer(adler + (uint64)(uint32)buf[15])) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 15) + 1);
   };
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 15) + 1) by simp() using {
    sum2 == at(byte_15, sum2 + (adler + (uint64)(uint32)buf[15]));
    at(byte_15, to_integer(sum2 + (adler + (uint64)(uint32)buf[15]))) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 15) + 1);
   };
   have to_integer(adler) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 16)) by simp();
   have to_integer(sum2) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 16)) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 16), (zlib_batch_count(n) + 16)) by simp();
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 16)) by simp();
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 16)) by simp();

     apply(zlib_batch_prefix_step(n));
     apply(zlib_batch_prefix_limit(n));
     apply(zlib_batch_nonempty_prefix(n));
     have defined(zlib_batch_count(n) + 16) by simp();
     execute_until(assignment(buf, 1));
     mark before_advance;
     step();
     have buf == at(before_advance, buf) + 16 by simp();
     have at(loop(2).entry, buf) + zlib_batch_count(n) + 16 == at(loop(2).entry, buf) + (zlib_batch_count(n) + 16) by normalize() using { defined(zlib_batch_count(n) + 16); };
     have buf == at(loop(2).entry, buf) + zlib_batch_count(n - 1u32) by simp() using {
      buf == at(before_advance, buf) + 16;
      at(before_advance, buf) == at(loop(2).entry, buf) + zlib_batch_count(n);
      at(loop(2).entry, buf) + zlib_batch_count(n) + 16 == at(loop(2).entry, buf) + (zlib_batch_count(n) + 16);
      zlib_batch_count(n - 1u32) == zlib_batch_count(n) + 16;
     };
     have to_integer(adler) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), zlib_batch_count(n - 1u32)) by simp() using {
      to_integer(adler) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), zlib_batch_count(n) + 16);
      zlib_batch_count(n - 1u32) == zlib_batch_count(n) + 16;
     };
     have to_integer(sum2) == to_integer(at(loop(2).entry, sum2)) + to_integer(zlib_batch_count(n - 1u32)) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), zlib_batch_count(n - 1u32), zlib_batch_count(n - 1u32)) by simp() using {
      to_integer(sum2) == to_integer(at(loop(2).entry, sum2)) + to_integer(zlib_batch_count(n) + 16) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), zlib_batch_count(n) + 16, zlib_batch_count(n) + 16);
      zlib_batch_count(n - 1u32) == zlib_batch_count(n) + 16;
     };
     step(); step(); step();
     have n == at(before_advance, n) - 1u32 by simp();
     have len == at(before_block, len) by simp();
     apply(zlib_full_stream_capacity_step(at(before_advance, n), len));
     have 16u64 * (uint64)n + len == at(before_block, 16u64 * (uint64)n + len) - 16u64 by simp() using {
      n == at(before_advance, n) - 1u32;
      len == at(before_block, len);
      at(before_advance, 16u64 * (uint64)(n - 1u32)) + len == at(before_advance, 16u64 * (uint64)n) + len - 16u64;
     };
     have 16u64 * (uint64)n + len <= at(before_block, 16u64 * (uint64)n + len) - 16u64 by simp() using {
      16u64 * (uint64)n + len == at(before_block, 16u64 * (uint64)n + len) - 16u64;
     };
     have 16u64 * (uint64)n + len <= 2147483647u64 by simp() using {
      n == at(before_advance, n) - 1u32;
      at(before_advance, 16u64 * (uint64)(n - 1u32)) + len <= 2147483647u64;
     };
     have 16u64 * (uint64)n + len <= 9223372036854775807u64 by arithmetic() using {
      16u64 * (uint64)n + len <= 2147483647u64;
      n <= 347u32; len <= 2147478095u64;
     };
     have buf == at(before_block, buf) + 16 by simp();
     have 16u64 <= at(before_block, 16u64 * (uint64)n + len) by arithmetic() using {
      16u64 <= at(before_block, 16u64 * (uint64)n);
      at(before_block, 16u64 * (uint64)n) <= 5552u64;
      len <= 2147478095u64;
      len == at(before_block, len);
     };
     have viewable(buf[0u64..16u64 * (uint64)n + len]) by {
      transport(at(before_block, viewable(buf[0u64..16u64 * (uint64)n + len])), viewable(buf[0u64..16u64 * (uint64)n + len])) using {
       at(before_block, viewable(buf[0u64..16u64 * (uint64)n + len]));
       buf == at(before_block, buf) + 16;
       16u64 <= at(before_block, 16u64 * (uint64)n + len);
       16u64 * (uint64)n + len <= at(before_block, 16u64 * (uint64)n + len) - 16u64;
       16u64 * (uint64)n + len <= 9223372036854775807u64;
      };
     }
     mark after_counter;
     if n == 0u32 {
      step(); step();
      have viewable(buf[0u64..16u64 * (uint64)n + len]) by {
       transport(at(after_counter, viewable(buf[0u64..16u64 * (uint64)n + len])), viewable(buf[0u64..16u64 * (uint64)n + len])) using {
        at(after_counter, viewable(buf[0u64..16u64 * (uint64)n + len]));
        buf == at(after_counter, buf); n == at(after_counter, n); len == at(after_counter, len);
        16u64 * (uint64)n + len <= 9223372036854775807u64;
       };
      }
     } else {
      step(); execute_until(back_edge());
      apply(zlib_batch_positive(n));
      have n <= 347u32 by assumption();
      have len == at(loop(2).entry, len) by normalize();
      have at(loop(2).entry, len) <= 2147483647u64 by assumption();
      apply(zlib_batch_remaining_limit(n));
      unfold(zlib_batch_remaining(n));
      have 16u64 * (uint64)n <= 5552u64 by assumption();
      have 16u64 * (uint64)n <= 9223372036854775807u64 by arithmetic() using { 16u64 * (uint64)n <= 5552u64; };
      apply(zlib_batch_cursor(at(loop(2).entry, buf), n));
      have buf == at(loop(2).entry, buf) + (5552u64 - zlib_batch_remaining(n)) by simp() using {
       buf == at(loop(2).entry, buf) + zlib_batch_count(n);
       at(loop(2).entry, buf) + zlib_batch_count(n) == at(loop(2).entry, buf) + (5552u64 - zlib_batch_remaining(n));
      };
      apply(zlib_batch_capacity_step(at(before_advance, n)));
      have n == at(before_advance, n) - 1u32 by simp();
      have 16u64 * (uint64)n == at(before_advance, 16u64 * (uint64)n) - 16u64 by simp() using {
       n == at(before_advance, n) - 1u32;
       at(before_advance, 16u64 * (uint64)(n - 1u32)) == at(before_advance, 16u64 * (uint64)n - 16u64);
      };
      have 16u64 * (uint64)n <= at(before_block, 16u64 * (uint64)n) - 16u64 by simp() using {
       16u64 * (uint64)n == at(before_advance, 16u64 * (uint64)n) - 16u64;
      };
      have buf == at(before_block, buf) + 16 by simp();
      have viewable(buf[0u64..16u64 * (uint64)n]) by {
       transport(at(before_block, viewable(buf[0u64..16u64 * (uint64)n])), viewable(buf[0u64..16u64 * (uint64)n])) using {
        buf == at(before_block, buf) + 16;
        at(before_block, viewable(buf[0u64..16u64 * (uint64)n]));
        16u64 <= at(before_advance, 16u64 * (uint64)n);
        16u64 * (uint64)n <= at(before_block, 16u64 * (uint64)n) - 16u64;
        16u64 * (uint64)n <= 5552u64;
        16u64 * (uint64)n <= 9223372036854775807u64;
       };
      }
      have zlib_batch_count(n) == at(before_advance, zlib_batch_count(n) + 16) by simp() using {
       n == at(before_advance, n) - 1u32;
       at(before_advance, zlib_batch_count(n - 1u32)) == at(before_advance, zlib_batch_count(n) + 16);
      };
      have adler == at(before_advance, adler) by simp();
      have sum2 == at(before_advance, sum2) by simp();
      have to_integer(adler) <= 65520 + 255 * to_integer(zlib_batch_count(n)) by simp() using {
       adler == at(before_advance, adler);
       at(before_advance, to_integer(adler) <= 65520 + 255 * to_integer(zlib_batch_count(n) + 16));
       zlib_batch_count(n) == at(before_advance, zlib_batch_count(n) + 16);
      };
      have to_integer(sum2) <= 65520 + 1481280 * to_integer(zlib_batch_count(n)) by simp() using {
       sum2 == at(before_advance, sum2);
       at(before_advance, to_integer(sum2) <= 65520 + 1481280 * to_integer(zlib_batch_count(n) + 16));
       zlib_batch_count(n) == at(before_advance, zlib_batch_count(n) + 16);
      };
      apply(uint32_to_integer_bounds(n));
      apply(uint32_subtract_to_integer(at(before_advance, n), 1u32));
      have to_integer(n) == at(before_advance, to_integer(n)) - 1 by simp() using {
       n == at(before_advance, n) - 1u32;
       to_integer(at(before_advance, n) - 1u32) == to_integer(at(before_advance, n)) - to_integer(1u32);
      };
      have to_integer(n) < at(before_advance, to_integer(n)) by arithmetic() using {
       to_integer(n) == at(before_advance, to_integer(n)) - 1;
      };
      have viewable(buf[0u64..16u64 * (uint64)n + len]) by {
       transport(at(after_counter, viewable(buf[0u64..16u64 * (uint64)n + len])), viewable(buf[0u64..16u64 * (uint64)n + len])) using {
        at(after_counter, viewable(buf[0u64..16u64 * (uint64)n + len]));
        buf == at(after_counter, buf); n == at(after_counter, n); len == at(after_counter, len);
        16u64 * (uint64)n + len <= 9223372036854775807u64;
       };
      }
      close_invariants() by assumption();
     }
    }
   }
   have n == 0u32 by simp();
   apply(zlib_batch_prefix_final());
   have zlib_batch_count(n) == 5552 by simp();
   have len == at(batch_entry, len) - 5552u64 by simp();
   have to_integer(adler) == to_integer(at(batch_entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), 5552) by simp() using {
    to_integer(adler) == to_integer(at(batch_entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), zlib_batch_count(n));
    zlib_batch_count(n) == 5552;
   };
   have to_integer(zlib_batch_count(n)) == 5552 by simp() using { zlib_batch_count(n) == 5552; };
   have adler_weighted_sum(at(loop(2).entry, buf), zlib_batch_count(n), zlib_batch_count(n)) == adler_weighted_sum(at(loop(2).entry, buf), 5552, 5552) by simp() using { zlib_batch_count(n) == 5552; };
   have to_integer(sum2) == to_integer(at(batch_entry, sum2)) + 5552 * to_integer(at(batch_entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), 5552, 5552) by {
    have to_integer(zlib_batch_count(n)) * to_integer(at(batch_entry, adler)) == 5552 * to_integer(at(batch_entry, adler)) by { rewrite(to_integer(zlib_batch_count(n)) == 5552); normalize(); }
    arithmetic() using {
     to_integer(sum2) == to_integer(at(batch_entry, sum2)) + to_integer(zlib_batch_count(n)) * to_integer(at(batch_entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), zlib_batch_count(n), zlib_batch_count(n));
     to_integer(zlib_batch_count(n)) * to_integer(at(batch_entry, adler)) == 5552 * to_integer(at(batch_entry, adler));
     adler_weighted_sum(at(loop(2).entry, buf), zlib_batch_count(n), zlib_batch_count(n)) == adler_weighted_sum(at(loop(2).entry, buf), 5552, 5552);
    };
   }
   have at(batch_entry, len) <= old(len) by assumption();
   have old(len) - at(batch_entry, len) <= 2147483647u64 by arithmetic() using { at(batch_entry, len) <= old(len); old(len) <= 2147483647u64; };
   apply(zlib_full_prefix_observation(old(len), at(batch_entry, len)));
   apply(zlib_full_prefix_pointer(old(buf), old(len), at(batch_entry, len)));
   have at(loop(2).entry, buf) == old(buf) + zlib_prefix_count(old(len), at(batch_entry, len)) by simp() using {
    at(batch_entry, buf) == old(buf) + (old(len) - at(batch_entry, len));
    old(buf) + (old(len) - at(batch_entry, len)) == old(buf) + zlib_prefix_count(old(len), at(batch_entry, len));
   };
   have to_integer(adler) == to_integer(at(batch_entry, adler)) + adler_byte_sum(old(buf) + zlib_prefix_count(old(len), at(batch_entry, len)), 5552) by {
    rewrite(old(buf) + zlib_prefix_count(old(len), at(batch_entry, len)) == at(loop(2).entry, buf)); assumption();
   }
   have to_integer(sum2) == to_integer(at(batch_entry, sum2)) + to_integer(5552) * to_integer(at(batch_entry, adler)) + adler_weighted_sum(old(buf) + zlib_prefix_count(old(len), at(batch_entry, len)), 5552, 5552) by {
    rewrite(old(buf) + zlib_prefix_count(old(len), at(batch_entry, len)) == at(loop(2).entry, buf)); assumption();
   }
   have 5552u64 <= at(batch_entry, len) by assumption();
   apply(zlib_full_chunk_bound(old(len), at(batch_entry, len), 5552u64));
   have zlib_prefix_count(old(len), at(batch_entry, len)) <= 2147483647 - 5552 by simp();
   have defined(zlib_prefix_count(old(len), at(batch_entry, len)) + 5552) by simp();
   apply(zlib_seeded_batch_concat(old(buf), zlib_prefix_count(old(len), at(batch_entry, len)), 5552, adler, sum2, at(batch_entry, adler), at(batch_entry, sum2)));
   apply(zlib_seeded_reduced_components(old(buf) + zlib_prefix_count(old(len), at(batch_entry, len)), 5552, adler, sum2, at(batch_entry, adler), at(batch_entry, sum2)));
   apply(zlib_full_stream_prefix_step(old(len), at(batch_entry, len), 5552u64));
   have zlib_prefix_count(old(len), len) == zlib_prefix_count(old(len), at(batch_entry, len)) + 5552 by simp() using {
    len == at(batch_entry, len) - 5552u64;
    zlib_prefix_count(old(len), at(batch_entry, len) - 5552u64) == zlib_prefix_count(old(len), at(batch_entry, len)) + (int32)(uint32)5552u64;
   };
   have viewable(buf[0u64..len]) by simp() using {
    viewable(buf[0u64..16u64 * (uint64)n + len]); n == 0u32;
   };
   mark before_reductions;
   step(); step();
   have adler == at(before_reductions, adler % 65521u64) by simp();
   have sum2 == at(before_reductions, sum2 % 65521u64) by simp();
   have to_integer(adler) == adler_spec_a(old(buf), zlib_prefix_count(old(len), at(batch_entry, len)) + 5552, 1) by simp() using {
    adler == at(before_reductions, adler % 65521u64);
    at(before_reductions, to_integer(adler % 65521u64)) == adler_spec_a(old(buf), zlib_prefix_count(old(len), at(batch_entry, len)) + 5552, 1);
   };
   have to_integer(sum2) == adler_spec_b(old(buf), zlib_prefix_count(old(len), at(batch_entry, len)) + 5552, 1, 0) by simp() using {
    sum2 == at(before_reductions, sum2 % 65521u64);
    at(before_reductions, to_integer(sum2 % 65521u64)) == adler_spec_b(old(buf), zlib_prefix_count(old(len), at(batch_entry, len)) + 5552, 1, 0);
   };
   have to_integer(adler) == adler_spec_a(old(buf), zlib_prefix_count(old(len), len), 1) by { rewrite(zlib_prefix_count(old(len), len) == zlib_prefix_count(old(len), at(batch_entry, len)) + 5552); assumption(); }
   have to_integer(sum2) == adler_spec_b(old(buf), zlib_prefix_count(old(len), len), 1, 0) by { rewrite(zlib_prefix_count(old(len), len) == zlib_prefix_count(old(len), at(batch_entry, len)) + 5552); assumption(); }
   have adler <= 65520u64 by simp() using { adler == at(before_reductions, adler % 65521u64); at(before_reductions, adler % 65521u64 <= 65520u64); };
   have sum2 <= 65520u64 by simp() using { sum2 == at(before_reductions, sum2 % 65521u64); at(before_reductions, sum2 % 65521u64 <= 65520u64); };
   have buf == at(batch_entry, buf) + 5552 by simp() using { buf == at(loop(2).entry, buf) + zlib_batch_count(n); zlib_batch_count(n) == 5552; };
   apply(zlib_full_stream_remaining_step(old(len), at(batch_entry, len), 5552u64));
   have len <= old(len) by simp() using { len == at(batch_entry, len) - 5552u64; at(batch_entry, len) - 5552u64 <= old(len); };
   have old(len) - len <= 2147483647u64 by arithmetic() using { len <= old(len); old(len) <= 2147483647u64; };
   apply(zlib_full_prefix_pointer(old(buf), old(len), len));
   have old(buf) + zlib_prefix_count(old(len), at(batch_entry, len)) + 5552 == old(buf) + (zlib_prefix_count(old(len), at(batch_entry, len)) + 5552) by normalize() using { defined(zlib_prefix_count(old(len), at(batch_entry, len)) + 5552); };
   have buf == old(buf) + (old(len) - len) by simp() using {
    buf == at(batch_entry, buf) + 5552;
    at(batch_entry, buf) == old(buf) + zlib_prefix_count(old(len), at(batch_entry, len));
    old(buf) + zlib_prefix_count(old(len), at(batch_entry, len)) + 5552 == old(buf) + (zlib_prefix_count(old(len), at(batch_entry, len)) + 5552);
    zlib_prefix_count(old(len), len) == zlib_prefix_count(old(len), at(batch_entry, len)) + 5552;
    old(buf) + (old(len) - len) == old(buf) + zlib_prefix_count(old(len), len);
   };
   have len <= 9223372036854775807u64 by arithmetic() using { len <= old(len); old(len) <= 2147483647u64; };
   have viewable(buf[0u64..len]) by {
    transport(at(before_reductions, viewable(buf[0u64..len])), viewable(buf[0u64..len])) using {
     at(before_reductions, viewable(buf[0u64..len]));
     buf == at(before_reductions, buf); len == at(before_reductions, len);
     len <= 9223372036854775807u64;
    };
   }

   have to_integer(len) == at(batch_entry, to_integer(len)) - 5552 by simp() using {
    len == at(batch_entry, len) - 5552u64;
    to_integer(at(batch_entry, len) - 5552u64) == at(batch_entry, to_integer(len)) - 5552;
   };
   apply(uint64_to_integer_bounds(len));
   have to_integer(len) < at(batch_entry, to_integer(len)) by arithmetic() using { to_integer(len) == at(batch_entry, to_integer(len)) - 5552; };
   close_invariants() by assumption();
  }

 }
 have len < 5552u64 by assumption();
 if len == 0u64 {
  have zlib_prefix_count(old(len), len) == old((int32)(uint32)len) by { unfold(zlib_prefix_count(old(len), len)); simp() using { len == 0u64; }; }
  have to_integer(adler) == adler_spec_a(old(buf), old((int32)(uint32)len), 1) by simp() using { to_integer(adler) == adler_spec_a(old(buf), zlib_prefix_count(old(len), len), 1); zlib_prefix_count(old(len), len) == old((int32)(uint32)len); };
  have to_integer(sum2) == adler_spec_b(old(buf), old((int32)(uint32)len), 1, 0) by simp() using { to_integer(sum2) == adler_spec_b(old(buf), zlib_prefix_count(old(len), len), 1, 0); zlib_prefix_count(old(len), len) == old((int32)(uint32)len); };
  have adler <= 65535u64 by arithmetic() using { adler <= 65520u64; };
  have sum2 <= 65535u64 by arithmetic() using { sum2 <= 65520u64; };
  apply(uint64_pack_uint16_to_integer(adler, sum2));
  have to_integer(adler | (sum2 << 16)) == adler_spec_checksum(old(buf), old((int32)(uint32)len), 1, 0) by {
   unfold(adler_spec_checksum(old(buf), old((int32)(uint32)len), 1, 0));
   arithmetic() using { to_integer(adler | (sum2 << 16)) == to_integer(adler) + 65536 * to_integer(sum2); to_integer(adler) == adler_spec_a(old(buf), old((int32)(uint32)len), 1); to_integer(sum2) == adler_spec_b(old(buf), old((int32)(uint32)len), 1, 0); };
  }
  execute(); simp();
 } else {
  have len <= 5551u64 by arithmetic() using { len < 5552u64; };
  have len <= 9223372036854775807u64 by arithmetic() using { len <= 5551u64; };
  // The remaining DO16 blocks start from the last batch's reduced seed.
  mark tail_entry;
  step(); execute_until(loop(3));
 loop {
  decreases to_integer(len);
  invariant at(loop(3).entry, len) <= old(len);
  invariant at(loop(3).entry, buf) == old(buf) + (old(len) - at(loop(3).entry, len));
  invariant to_integer(at(loop(3).entry, adler)) == adler_spec_a(old(buf), zlib_prefix_count(old(len), at(loop(3).entry, len)), 1);
  invariant to_integer(at(loop(3).entry, sum2)) == adler_spec_b(old(buf), zlib_prefix_count(old(len), at(loop(3).entry, len)), 1, 0);

  invariant len <= at(loop(3).entry, len);
  invariant at(loop(3).entry, len) <= 5551u64;
  invariant at(loop(3).entry, adler) <= 65520u64;
  invariant at(loop(3).entry, sum2) <= 65520u64;
  invariant len <= old(len);
  invariant old(len) <= 2147483647u64;
  invariant buf == old(buf) + (old(len) - len);
  invariant at(loop(3).entry, len) - len <= 5551u64;
  invariant to_integer(len) <= 5551;
  invariant buf == at(loop(3).entry, buf) + (at(loop(3).entry, len) - len);
  invariant viewable(buf[0u64..len]);
  invariant to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), zlib_prefix_count(at(loop(3).entry, len), len));
  invariant to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer(zlib_prefix_count(at(loop(3).entry, len), len)) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), zlib_prefix_count(at(loop(3).entry, len), len), zlib_prefix_count(at(loop(3).entry, len), len));
  invariant to_integer(adler) <= 65520 + 255 * to_integer(zlib_prefix_count(at(loop(3).entry, len), len));
  invariant to_integer(sum2) <= 65520 + 1481280 * to_integer(zlib_prefix_count(at(loop(3).entry, len), len));
  initialize by {
   have len <= at(loop(3).entry, len) by simp();
   have len <= 9223372036854775807u64 by arithmetic() using { len <= 5551u64; };
   have at(loop(3).entry, len) - len == 0u64 by simp();
   apply(uint64_less_equal_to_integer(len, 5551u64));
   have adler == at(loop(3).entry, adler) by simp();
   have sum2 == at(loop(3).entry, sum2) by simp();
   apply(uint64_less_equal_to_integer(adler, 65520u64));
   apply(uint64_less_equal_to_integer(sum2, 65520u64));
   have zlib_prefix_count(at(loop(3).entry, len), len) == 0 by { unfold(zlib_prefix_count(at(loop(3).entry, len), len)); simp(); }
   apply(adler_sum_empty(at(loop(3).entry, buf), 0));
   have to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), 0) by arithmetic() using { to_integer(adler) == to_integer(at(loop(3).entry, adler)); adler_byte_sum(at(loop(3).entry, buf), 0) == 0; };
   have to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer(0) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), 0, 0) by arithmetic() using { to_integer(sum2) == to_integer(at(loop(3).entry, sum2)); adler_weighted_sum(at(loop(3).entry, buf), 0, 0) == 0; };
   have to_integer(adler) <= 65520 + 255 * to_integer(0) by arithmetic() using { to_integer(adler) <= 65520; };
   have to_integer(sum2) <= 65520 + 1481280 * to_integer(0) by arithmetic() using { to_integer(sum2) <= 65520; };
   have to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), zlib_prefix_count(at(loop(3).entry, len), len)) by { rewrite(zlib_prefix_count(at(loop(3).entry, len), len) == 0); assumption(); }
   have to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer(zlib_prefix_count(at(loop(3).entry, len), len)) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), zlib_prefix_count(at(loop(3).entry, len), len), zlib_prefix_count(at(loop(3).entry, len), len)) by { rewrite(zlib_prefix_count(at(loop(3).entry, len), len) == 0); assumption(); }
   have to_integer(adler) <= 65520 + 255 * to_integer(zlib_prefix_count(at(loop(3).entry, len), len)) by { rewrite(zlib_prefix_count(at(loop(3).entry, len), len) == 0); assumption(); }
   have to_integer(sum2) <= 65520 + 1481280 * to_integer(zlib_prefix_count(at(loop(3).entry, len), len)) by { rewrite(zlib_prefix_count(at(loop(3).entry, len), len) == 0); assumption(); }
   simp();
  }
  preserve by {
   have 16u64 <= len by simp();
   have len <= 5551u64 by arithmetic() using { len <= at(loop(3).entry, len); at(loop(3).entry, len) <= 5551u64; };
   have len <= 9223372036854775807u64 by arithmetic() using { len <= 5551u64; };
   have 1u64 <= len by arithmetic() using { 16u64 <= len; };
   have viewable(buf[0u64..16u64]) by simp();
   apply(zlib_remaining_step(at(loop(3).entry, len), len, 16u64));
   have at(loop(3).entry, len) - len <= 2147483647u64 by arithmetic() using { at(loop(3).entry, len) - len <= 5551u64; };
   apply(zlib_full_prefix_observation(at(loop(3).entry, len), len));
   have at(loop(3).entry, len) - len < at(loop(3).entry, len) by arithmetic() using { 16u64 <= len; len <= at(loop(3).entry, len); at(loop(3).entry, len) <= 5551u64; };
   mark before_block;
   step();
   have len == at(before_block, len - 16u64) by simp();
   have to_integer(len) == at(before_block, to_integer(len)) - 16 by simp();
   execute_until(assignment(adler, 22));
   apply(zlib_block_read_bound(at(loop(3).entry, len), at(before_block, len), 0u64));
   apply(zlib_full_stream_tail_read_bound(old(len), at(before_block, len), 0u64));
   apply(zlib_block_lane(at(loop(3).entry, buf), at(loop(3).entry, len), at(before_block, len), 0));
   have buf[0] == at(loop(3).entry, buf)[zlib_prefix_count(at(loop(3).entry, len), at(before_block, len))] by simp() using {
    buf == at(loop(3).entry, buf) + (at(loop(3).entry, len) - at(before_block, len));
    (at(loop(3).entry, buf) + (at(loop(3).entry, len) - at(before_block, len)))[0] == at(loop(3).entry, buf)[zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 0];
   };
   apply(zlib_seeded_component_step(at(loop(3).entry, buf), zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)), adler, sum2, buf[0], at(loop(3).entry, adler), at(loop(3).entry, sum2)));
   have viewable(buf[0u64..1u64]) by simp();
   mark byte_0;
   step();
   execute_until(assignment(sum2, 22));
   step();
   have adler == at(byte_0, adler + (uint64)(uint32)buf[0]) by simp();
   have sum2 == at(byte_0, sum2 + (adler + (uint64)(uint32)buf[0])) by simp();
   have to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 1) by simp() using {
    adler == at(byte_0, adler + (uint64)(uint32)buf[0]);
    at(byte_0, to_integer(adler + (uint64)(uint32)buf[0])) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 1);
   };
   have to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer(zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 1) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 1, zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 1) by simp() using {
    sum2 == at(byte_0, sum2 + (adler + (uint64)(uint32)buf[0]));
    at(byte_0, to_integer(sum2 + (adler + (uint64)(uint32)buf[0]))) == to_integer(at(loop(3).entry, sum2)) + to_integer(zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 1) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 1, zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 1);
   };
   have to_integer(adler) <= 65520 + 255 * to_integer(zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 1) by simp() using {
    adler == at(byte_0, adler + (uint64)(uint32)buf[0]);
    at(byte_0, to_integer(adler + (uint64)(uint32)buf[0])) <= 65520 + 255 * to_integer(zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 1);
   };
   have to_integer(sum2) <= 65520 + 1481280 * to_integer(zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 1) by simp() using {
    sum2 == at(byte_0, sum2 + (adler + (uint64)(uint32)buf[0]));
    at(byte_0, to_integer(sum2 + (adler + (uint64)(uint32)buf[0]))) <= 65520 + 1481280 * to_integer(zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 1);
   };
   have to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 1)) by simp();
   have to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 1)) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 1), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 1)) by simp();
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 1)) by simp();
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 1)) by simp();
   execute_until(assignment(adler, 23));
   apply(zlib_block_read_bound(at(loop(3).entry, len), at(before_block, len), 1u64));
   apply(zlib_full_stream_tail_read_bound(old(len), at(before_block, len), 1u64));
   apply(zlib_block_lane(at(loop(3).entry, buf), at(loop(3).entry, len), at(before_block, len), 1));
   have buf[1] == at(loop(3).entry, buf)[(zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 1)] by simp() using {
    buf == at(loop(3).entry, buf) + (at(loop(3).entry, len) - at(before_block, len));
    (at(loop(3).entry, buf) + (at(loop(3).entry, len) - at(before_block, len)))[1] == at(loop(3).entry, buf)[zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 1];
   };
   apply(zlib_seeded_component_step(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 1), adler, sum2, buf[1], at(loop(3).entry, adler), at(loop(3).entry, sum2)));
   mark byte_1;
   step();
   execute_until(assignment(sum2, 23));
   step();
   have adler == at(byte_1, adler + (uint64)(uint32)buf[1]) by simp();
   have sum2 == at(byte_1, sum2 + (adler + (uint64)(uint32)buf[1])) by simp();
   have to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 1) + 1) by simp() using {
    adler == at(byte_1, adler + (uint64)(uint32)buf[1]);
    at(byte_1, to_integer(adler + (uint64)(uint32)buf[1])) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 1) + 1);
   };
   have to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 1) + 1) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 1) + 1, (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 1) + 1) by simp() using {
    sum2 == at(byte_1, sum2 + (adler + (uint64)(uint32)buf[1]));
    at(byte_1, to_integer(sum2 + (adler + (uint64)(uint32)buf[1]))) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 1) + 1) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 1) + 1, (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 1) + 1);
   };
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 1) + 1) by simp() using {
    adler == at(byte_1, adler + (uint64)(uint32)buf[1]);
    at(byte_1, to_integer(adler + (uint64)(uint32)buf[1])) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 1) + 1);
   };
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 1) + 1) by simp() using {
    sum2 == at(byte_1, sum2 + (adler + (uint64)(uint32)buf[1]));
    at(byte_1, to_integer(sum2 + (adler + (uint64)(uint32)buf[1]))) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 1) + 1);
   };
   have to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 2)) by simp();
   have to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 2)) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 2), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 2)) by simp();
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 2)) by simp();
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 2)) by simp();
   execute_until(assignment(adler, 24));
   apply(zlib_block_read_bound(at(loop(3).entry, len), at(before_block, len), 2u64));
   apply(zlib_full_stream_tail_read_bound(old(len), at(before_block, len), 2u64));
   apply(zlib_block_lane(at(loop(3).entry, buf), at(loop(3).entry, len), at(before_block, len), 2));
   have buf[2] == at(loop(3).entry, buf)[(zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 2)] by simp() using {
    buf == at(loop(3).entry, buf) + (at(loop(3).entry, len) - at(before_block, len));
    (at(loop(3).entry, buf) + (at(loop(3).entry, len) - at(before_block, len)))[2] == at(loop(3).entry, buf)[zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 2];
   };
   apply(zlib_seeded_component_step(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 2), adler, sum2, buf[2], at(loop(3).entry, adler), at(loop(3).entry, sum2)));
   mark byte_2;
   step();
   execute_until(assignment(sum2, 24));
   step();
   have adler == at(byte_2, adler + (uint64)(uint32)buf[2]) by simp();
   have sum2 == at(byte_2, sum2 + (adler + (uint64)(uint32)buf[2])) by simp();
   have to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 2) + 1) by simp() using {
    adler == at(byte_2, adler + (uint64)(uint32)buf[2]);
    at(byte_2, to_integer(adler + (uint64)(uint32)buf[2])) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 2) + 1);
   };
   have to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 2) + 1) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 2) + 1, (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 2) + 1) by simp() using {
    sum2 == at(byte_2, sum2 + (adler + (uint64)(uint32)buf[2]));
    at(byte_2, to_integer(sum2 + (adler + (uint64)(uint32)buf[2]))) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 2) + 1) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 2) + 1, (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 2) + 1);
   };
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 2) + 1) by simp() using {
    adler == at(byte_2, adler + (uint64)(uint32)buf[2]);
    at(byte_2, to_integer(adler + (uint64)(uint32)buf[2])) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 2) + 1);
   };
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 2) + 1) by simp() using {
    sum2 == at(byte_2, sum2 + (adler + (uint64)(uint32)buf[2]));
    at(byte_2, to_integer(sum2 + (adler + (uint64)(uint32)buf[2]))) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 2) + 1);
   };
   have to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 3)) by simp();
   have to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 3)) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 3), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 3)) by simp();
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 3)) by simp();
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 3)) by simp();
   execute_until(assignment(adler, 25));
   apply(zlib_block_read_bound(at(loop(3).entry, len), at(before_block, len), 3u64));
   apply(zlib_full_stream_tail_read_bound(old(len), at(before_block, len), 3u64));
   apply(zlib_block_lane(at(loop(3).entry, buf), at(loop(3).entry, len), at(before_block, len), 3));
   have buf[3] == at(loop(3).entry, buf)[(zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 3)] by simp() using {
    buf == at(loop(3).entry, buf) + (at(loop(3).entry, len) - at(before_block, len));
    (at(loop(3).entry, buf) + (at(loop(3).entry, len) - at(before_block, len)))[3] == at(loop(3).entry, buf)[zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 3];
   };
   apply(zlib_seeded_component_step(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 3), adler, sum2, buf[3], at(loop(3).entry, adler), at(loop(3).entry, sum2)));
   mark byte_3;
   step();
   execute_until(assignment(sum2, 25));
   step();
   have adler == at(byte_3, adler + (uint64)(uint32)buf[3]) by simp();
   have sum2 == at(byte_3, sum2 + (adler + (uint64)(uint32)buf[3])) by simp();
   have to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 3) + 1) by simp() using {
    adler == at(byte_3, adler + (uint64)(uint32)buf[3]);
    at(byte_3, to_integer(adler + (uint64)(uint32)buf[3])) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 3) + 1);
   };
   have to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 3) + 1) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 3) + 1, (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 3) + 1) by simp() using {
    sum2 == at(byte_3, sum2 + (adler + (uint64)(uint32)buf[3]));
    at(byte_3, to_integer(sum2 + (adler + (uint64)(uint32)buf[3]))) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 3) + 1) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 3) + 1, (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 3) + 1);
   };
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 3) + 1) by simp() using {
    adler == at(byte_3, adler + (uint64)(uint32)buf[3]);
    at(byte_3, to_integer(adler + (uint64)(uint32)buf[3])) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 3) + 1);
   };
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 3) + 1) by simp() using {
    sum2 == at(byte_3, sum2 + (adler + (uint64)(uint32)buf[3]));
    at(byte_3, to_integer(sum2 + (adler + (uint64)(uint32)buf[3]))) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 3) + 1);
   };
   have to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 4)) by simp();
   have to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 4)) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 4), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 4)) by simp();
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 4)) by simp();
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 4)) by simp();
   execute_until(assignment(adler, 26));
   apply(zlib_block_read_bound(at(loop(3).entry, len), at(before_block, len), 4u64));
   apply(zlib_full_stream_tail_read_bound(old(len), at(before_block, len), 4u64));
   apply(zlib_block_lane(at(loop(3).entry, buf), at(loop(3).entry, len), at(before_block, len), 4));
   have buf[4] == at(loop(3).entry, buf)[(zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 4)] by simp() using {
    buf == at(loop(3).entry, buf) + (at(loop(3).entry, len) - at(before_block, len));
    (at(loop(3).entry, buf) + (at(loop(3).entry, len) - at(before_block, len)))[4] == at(loop(3).entry, buf)[zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 4];
   };
   apply(zlib_seeded_component_step(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 4), adler, sum2, buf[4], at(loop(3).entry, adler), at(loop(3).entry, sum2)));
   mark byte_4;
   step();
   execute_until(assignment(sum2, 26));
   step();
   have adler == at(byte_4, adler + (uint64)(uint32)buf[4]) by simp();
   have sum2 == at(byte_4, sum2 + (adler + (uint64)(uint32)buf[4])) by simp();
   have to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 4) + 1) by simp() using {
    adler == at(byte_4, adler + (uint64)(uint32)buf[4]);
    at(byte_4, to_integer(adler + (uint64)(uint32)buf[4])) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 4) + 1);
   };
   have to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 4) + 1) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 4) + 1, (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 4) + 1) by simp() using {
    sum2 == at(byte_4, sum2 + (adler + (uint64)(uint32)buf[4]));
    at(byte_4, to_integer(sum2 + (adler + (uint64)(uint32)buf[4]))) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 4) + 1) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 4) + 1, (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 4) + 1);
   };
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 4) + 1) by simp() using {
    adler == at(byte_4, adler + (uint64)(uint32)buf[4]);
    at(byte_4, to_integer(adler + (uint64)(uint32)buf[4])) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 4) + 1);
   };
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 4) + 1) by simp() using {
    sum2 == at(byte_4, sum2 + (adler + (uint64)(uint32)buf[4]));
    at(byte_4, to_integer(sum2 + (adler + (uint64)(uint32)buf[4]))) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 4) + 1);
   };
   have to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 5)) by simp();
   have to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 5)) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 5), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 5)) by simp();
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 5)) by simp();
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 5)) by simp();
   execute_until(assignment(adler, 27));
   apply(zlib_block_read_bound(at(loop(3).entry, len), at(before_block, len), 5u64));
   apply(zlib_full_stream_tail_read_bound(old(len), at(before_block, len), 5u64));
   apply(zlib_block_lane(at(loop(3).entry, buf), at(loop(3).entry, len), at(before_block, len), 5));
   have buf[5] == at(loop(3).entry, buf)[(zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 5)] by simp() using {
    buf == at(loop(3).entry, buf) + (at(loop(3).entry, len) - at(before_block, len));
    (at(loop(3).entry, buf) + (at(loop(3).entry, len) - at(before_block, len)))[5] == at(loop(3).entry, buf)[zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 5];
   };
   apply(zlib_seeded_component_step(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 5), adler, sum2, buf[5], at(loop(3).entry, adler), at(loop(3).entry, sum2)));
   mark byte_5;
   step();
   execute_until(assignment(sum2, 27));
   step();
   have adler == at(byte_5, adler + (uint64)(uint32)buf[5]) by simp();
   have sum2 == at(byte_5, sum2 + (adler + (uint64)(uint32)buf[5])) by simp();
   have to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 5) + 1) by simp() using {
    adler == at(byte_5, adler + (uint64)(uint32)buf[5]);
    at(byte_5, to_integer(adler + (uint64)(uint32)buf[5])) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 5) + 1);
   };
   have to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 5) + 1) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 5) + 1, (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 5) + 1) by simp() using {
    sum2 == at(byte_5, sum2 + (adler + (uint64)(uint32)buf[5]));
    at(byte_5, to_integer(sum2 + (adler + (uint64)(uint32)buf[5]))) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 5) + 1) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 5) + 1, (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 5) + 1);
   };
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 5) + 1) by simp() using {
    adler == at(byte_5, adler + (uint64)(uint32)buf[5]);
    at(byte_5, to_integer(adler + (uint64)(uint32)buf[5])) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 5) + 1);
   };
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 5) + 1) by simp() using {
    sum2 == at(byte_5, sum2 + (adler + (uint64)(uint32)buf[5]));
    at(byte_5, to_integer(sum2 + (adler + (uint64)(uint32)buf[5]))) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 5) + 1);
   };
   have to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 6)) by simp();
   have to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 6)) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 6), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 6)) by simp();
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 6)) by simp();
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 6)) by simp();
   execute_until(assignment(adler, 28));
   apply(zlib_block_read_bound(at(loop(3).entry, len), at(before_block, len), 6u64));
   apply(zlib_full_stream_tail_read_bound(old(len), at(before_block, len), 6u64));
   apply(zlib_block_lane(at(loop(3).entry, buf), at(loop(3).entry, len), at(before_block, len), 6));
   have buf[6] == at(loop(3).entry, buf)[(zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 6)] by simp() using {
    buf == at(loop(3).entry, buf) + (at(loop(3).entry, len) - at(before_block, len));
    (at(loop(3).entry, buf) + (at(loop(3).entry, len) - at(before_block, len)))[6] == at(loop(3).entry, buf)[zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 6];
   };
   apply(zlib_seeded_component_step(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 6), adler, sum2, buf[6], at(loop(3).entry, adler), at(loop(3).entry, sum2)));
   mark byte_6;
   step();
   execute_until(assignment(sum2, 28));
   step();
   have adler == at(byte_6, adler + (uint64)(uint32)buf[6]) by simp();
   have sum2 == at(byte_6, sum2 + (adler + (uint64)(uint32)buf[6])) by simp();
   have to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 6) + 1) by simp() using {
    adler == at(byte_6, adler + (uint64)(uint32)buf[6]);
    at(byte_6, to_integer(adler + (uint64)(uint32)buf[6])) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 6) + 1);
   };
   have to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 6) + 1) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 6) + 1, (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 6) + 1) by simp() using {
    sum2 == at(byte_6, sum2 + (adler + (uint64)(uint32)buf[6]));
    at(byte_6, to_integer(sum2 + (adler + (uint64)(uint32)buf[6]))) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 6) + 1) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 6) + 1, (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 6) + 1);
   };
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 6) + 1) by simp() using {
    adler == at(byte_6, adler + (uint64)(uint32)buf[6]);
    at(byte_6, to_integer(adler + (uint64)(uint32)buf[6])) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 6) + 1);
   };
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 6) + 1) by simp() using {
    sum2 == at(byte_6, sum2 + (adler + (uint64)(uint32)buf[6]));
    at(byte_6, to_integer(sum2 + (adler + (uint64)(uint32)buf[6]))) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 6) + 1);
   };
   have to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 7)) by simp();
   have to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 7)) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 7), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 7)) by simp();
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 7)) by simp();
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 7)) by simp();
   execute_until(assignment(adler, 29));
   apply(zlib_block_read_bound(at(loop(3).entry, len), at(before_block, len), 7u64));
   apply(zlib_full_stream_tail_read_bound(old(len), at(before_block, len), 7u64));
   apply(zlib_block_lane(at(loop(3).entry, buf), at(loop(3).entry, len), at(before_block, len), 7));
   have buf[7] == at(loop(3).entry, buf)[(zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 7)] by simp() using {
    buf == at(loop(3).entry, buf) + (at(loop(3).entry, len) - at(before_block, len));
    (at(loop(3).entry, buf) + (at(loop(3).entry, len) - at(before_block, len)))[7] == at(loop(3).entry, buf)[zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 7];
   };
   apply(zlib_seeded_component_step(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 7), adler, sum2, buf[7], at(loop(3).entry, adler), at(loop(3).entry, sum2)));
   mark byte_7;
   step();
   execute_until(assignment(sum2, 29));
   step();
   have adler == at(byte_7, adler + (uint64)(uint32)buf[7]) by simp();
   have sum2 == at(byte_7, sum2 + (adler + (uint64)(uint32)buf[7])) by simp();
   have to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 7) + 1) by simp() using {
    adler == at(byte_7, adler + (uint64)(uint32)buf[7]);
    at(byte_7, to_integer(adler + (uint64)(uint32)buf[7])) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 7) + 1);
   };
   have to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 7) + 1) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 7) + 1, (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 7) + 1) by simp() using {
    sum2 == at(byte_7, sum2 + (adler + (uint64)(uint32)buf[7]));
    at(byte_7, to_integer(sum2 + (adler + (uint64)(uint32)buf[7]))) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 7) + 1) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 7) + 1, (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 7) + 1);
   };
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 7) + 1) by simp() using {
    adler == at(byte_7, adler + (uint64)(uint32)buf[7]);
    at(byte_7, to_integer(adler + (uint64)(uint32)buf[7])) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 7) + 1);
   };
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 7) + 1) by simp() using {
    sum2 == at(byte_7, sum2 + (adler + (uint64)(uint32)buf[7]));
    at(byte_7, to_integer(sum2 + (adler + (uint64)(uint32)buf[7]))) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 7) + 1);
   };
   have to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 8)) by simp();
   have to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 8)) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 8), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 8)) by simp();
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 8)) by simp();
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 8)) by simp();
   execute_until(assignment(adler, 30));
   apply(zlib_block_read_bound(at(loop(3).entry, len), at(before_block, len), 8u64));
   apply(zlib_full_stream_tail_read_bound(old(len), at(before_block, len), 8u64));
   apply(zlib_block_lane(at(loop(3).entry, buf), at(loop(3).entry, len), at(before_block, len), 8));
   have buf[8] == at(loop(3).entry, buf)[(zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 8)] by simp() using {
    buf == at(loop(3).entry, buf) + (at(loop(3).entry, len) - at(before_block, len));
    (at(loop(3).entry, buf) + (at(loop(3).entry, len) - at(before_block, len)))[8] == at(loop(3).entry, buf)[zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 8];
   };
   apply(zlib_seeded_component_step(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 8), adler, sum2, buf[8], at(loop(3).entry, adler), at(loop(3).entry, sum2)));
   mark byte_8;
   step();
   execute_until(assignment(sum2, 30));
   step();
   have adler == at(byte_8, adler + (uint64)(uint32)buf[8]) by simp();
   have sum2 == at(byte_8, sum2 + (adler + (uint64)(uint32)buf[8])) by simp();
   have to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 8) + 1) by simp() using {
    adler == at(byte_8, adler + (uint64)(uint32)buf[8]);
    at(byte_8, to_integer(adler + (uint64)(uint32)buf[8])) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 8) + 1);
   };
   have to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 8) + 1) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 8) + 1, (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 8) + 1) by simp() using {
    sum2 == at(byte_8, sum2 + (adler + (uint64)(uint32)buf[8]));
    at(byte_8, to_integer(sum2 + (adler + (uint64)(uint32)buf[8]))) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 8) + 1) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 8) + 1, (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 8) + 1);
   };
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 8) + 1) by simp() using {
    adler == at(byte_8, adler + (uint64)(uint32)buf[8]);
    at(byte_8, to_integer(adler + (uint64)(uint32)buf[8])) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 8) + 1);
   };
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 8) + 1) by simp() using {
    sum2 == at(byte_8, sum2 + (adler + (uint64)(uint32)buf[8]));
    at(byte_8, to_integer(sum2 + (adler + (uint64)(uint32)buf[8]))) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 8) + 1);
   };
   have to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 9)) by simp();
   have to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 9)) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 9), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 9)) by simp();
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 9)) by simp();
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 9)) by simp();
   execute_until(assignment(adler, 31));
   apply(zlib_block_read_bound(at(loop(3).entry, len), at(before_block, len), 9u64));
   apply(zlib_full_stream_tail_read_bound(old(len), at(before_block, len), 9u64));
   apply(zlib_block_lane(at(loop(3).entry, buf), at(loop(3).entry, len), at(before_block, len), 9));
   have buf[9] == at(loop(3).entry, buf)[(zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 9)] by simp() using {
    buf == at(loop(3).entry, buf) + (at(loop(3).entry, len) - at(before_block, len));
    (at(loop(3).entry, buf) + (at(loop(3).entry, len) - at(before_block, len)))[9] == at(loop(3).entry, buf)[zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 9];
   };
   apply(zlib_seeded_component_step(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 9), adler, sum2, buf[9], at(loop(3).entry, adler), at(loop(3).entry, sum2)));
   mark byte_9;
   step();
   execute_until(assignment(sum2, 31));
   step();
   have adler == at(byte_9, adler + (uint64)(uint32)buf[9]) by simp();
   have sum2 == at(byte_9, sum2 + (adler + (uint64)(uint32)buf[9])) by simp();
   have to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 9) + 1) by simp() using {
    adler == at(byte_9, adler + (uint64)(uint32)buf[9]);
    at(byte_9, to_integer(adler + (uint64)(uint32)buf[9])) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 9) + 1);
   };
   have to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 9) + 1) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 9) + 1, (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 9) + 1) by simp() using {
    sum2 == at(byte_9, sum2 + (adler + (uint64)(uint32)buf[9]));
    at(byte_9, to_integer(sum2 + (adler + (uint64)(uint32)buf[9]))) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 9) + 1) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 9) + 1, (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 9) + 1);
   };
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 9) + 1) by simp() using {
    adler == at(byte_9, adler + (uint64)(uint32)buf[9]);
    at(byte_9, to_integer(adler + (uint64)(uint32)buf[9])) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 9) + 1);
   };
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 9) + 1) by simp() using {
    sum2 == at(byte_9, sum2 + (adler + (uint64)(uint32)buf[9]));
    at(byte_9, to_integer(sum2 + (adler + (uint64)(uint32)buf[9]))) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 9) + 1);
   };
   have to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 10)) by simp();
   have to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 10)) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 10), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 10)) by simp();
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 10)) by simp();
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 10)) by simp();
   execute_until(assignment(adler, 32));
   apply(zlib_block_read_bound(at(loop(3).entry, len), at(before_block, len), 10u64));
   apply(zlib_full_stream_tail_read_bound(old(len), at(before_block, len), 10u64));
   apply(zlib_block_lane(at(loop(3).entry, buf), at(loop(3).entry, len), at(before_block, len), 10));
   have buf[10] == at(loop(3).entry, buf)[(zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 10)] by simp() using {
    buf == at(loop(3).entry, buf) + (at(loop(3).entry, len) - at(before_block, len));
    (at(loop(3).entry, buf) + (at(loop(3).entry, len) - at(before_block, len)))[10] == at(loop(3).entry, buf)[zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 10];
   };
   apply(zlib_seeded_component_step(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 10), adler, sum2, buf[10], at(loop(3).entry, adler), at(loop(3).entry, sum2)));
   mark byte_10;
   step();
   execute_until(assignment(sum2, 32));
   step();
   have adler == at(byte_10, adler + (uint64)(uint32)buf[10]) by simp();
   have sum2 == at(byte_10, sum2 + (adler + (uint64)(uint32)buf[10])) by simp();
   have to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 10) + 1) by simp() using {
    adler == at(byte_10, adler + (uint64)(uint32)buf[10]);
    at(byte_10, to_integer(adler + (uint64)(uint32)buf[10])) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 10) + 1);
   };
   have to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 10) + 1) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 10) + 1, (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 10) + 1) by simp() using {
    sum2 == at(byte_10, sum2 + (adler + (uint64)(uint32)buf[10]));
    at(byte_10, to_integer(sum2 + (adler + (uint64)(uint32)buf[10]))) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 10) + 1) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 10) + 1, (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 10) + 1);
   };
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 10) + 1) by simp() using {
    adler == at(byte_10, adler + (uint64)(uint32)buf[10]);
    at(byte_10, to_integer(adler + (uint64)(uint32)buf[10])) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 10) + 1);
   };
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 10) + 1) by simp() using {
    sum2 == at(byte_10, sum2 + (adler + (uint64)(uint32)buf[10]));
    at(byte_10, to_integer(sum2 + (adler + (uint64)(uint32)buf[10]))) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 10) + 1);
   };
   have to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 11)) by simp();
   have to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 11)) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 11), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 11)) by simp();
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 11)) by simp();
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 11)) by simp();
   execute_until(assignment(adler, 33));
   apply(zlib_block_read_bound(at(loop(3).entry, len), at(before_block, len), 11u64));
   apply(zlib_full_stream_tail_read_bound(old(len), at(before_block, len), 11u64));
   apply(zlib_block_lane(at(loop(3).entry, buf), at(loop(3).entry, len), at(before_block, len), 11));
   have buf[11] == at(loop(3).entry, buf)[(zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 11)] by simp() using {
    buf == at(loop(3).entry, buf) + (at(loop(3).entry, len) - at(before_block, len));
    (at(loop(3).entry, buf) + (at(loop(3).entry, len) - at(before_block, len)))[11] == at(loop(3).entry, buf)[zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 11];
   };
   apply(zlib_seeded_component_step(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 11), adler, sum2, buf[11], at(loop(3).entry, adler), at(loop(3).entry, sum2)));
   mark byte_11;
   step();
   execute_until(assignment(sum2, 33));
   step();
   have adler == at(byte_11, adler + (uint64)(uint32)buf[11]) by simp();
   have sum2 == at(byte_11, sum2 + (adler + (uint64)(uint32)buf[11])) by simp();
   have to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 11) + 1) by simp() using {
    adler == at(byte_11, adler + (uint64)(uint32)buf[11]);
    at(byte_11, to_integer(adler + (uint64)(uint32)buf[11])) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 11) + 1);
   };
   have to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 11) + 1) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 11) + 1, (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 11) + 1) by simp() using {
    sum2 == at(byte_11, sum2 + (adler + (uint64)(uint32)buf[11]));
    at(byte_11, to_integer(sum2 + (adler + (uint64)(uint32)buf[11]))) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 11) + 1) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 11) + 1, (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 11) + 1);
   };
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 11) + 1) by simp() using {
    adler == at(byte_11, adler + (uint64)(uint32)buf[11]);
    at(byte_11, to_integer(adler + (uint64)(uint32)buf[11])) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 11) + 1);
   };
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 11) + 1) by simp() using {
    sum2 == at(byte_11, sum2 + (adler + (uint64)(uint32)buf[11]));
    at(byte_11, to_integer(sum2 + (adler + (uint64)(uint32)buf[11]))) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 11) + 1);
   };
   have to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 12)) by simp();
   have to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 12)) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 12), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 12)) by simp();
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 12)) by simp();
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 12)) by simp();
   execute_until(assignment(adler, 34));
   apply(zlib_block_read_bound(at(loop(3).entry, len), at(before_block, len), 12u64));
   apply(zlib_full_stream_tail_read_bound(old(len), at(before_block, len), 12u64));
   apply(zlib_block_lane(at(loop(3).entry, buf), at(loop(3).entry, len), at(before_block, len), 12));
   have buf[12] == at(loop(3).entry, buf)[(zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 12)] by simp() using {
    buf == at(loop(3).entry, buf) + (at(loop(3).entry, len) - at(before_block, len));
    (at(loop(3).entry, buf) + (at(loop(3).entry, len) - at(before_block, len)))[12] == at(loop(3).entry, buf)[zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 12];
   };
   apply(zlib_seeded_component_step(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 12), adler, sum2, buf[12], at(loop(3).entry, adler), at(loop(3).entry, sum2)));
   mark byte_12;
   step();
   execute_until(assignment(sum2, 34));
   step();
   have adler == at(byte_12, adler + (uint64)(uint32)buf[12]) by simp();
   have sum2 == at(byte_12, sum2 + (adler + (uint64)(uint32)buf[12])) by simp();
   have to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 12) + 1) by simp() using {
    adler == at(byte_12, adler + (uint64)(uint32)buf[12]);
    at(byte_12, to_integer(adler + (uint64)(uint32)buf[12])) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 12) + 1);
   };
   have to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 12) + 1) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 12) + 1, (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 12) + 1) by simp() using {
    sum2 == at(byte_12, sum2 + (adler + (uint64)(uint32)buf[12]));
    at(byte_12, to_integer(sum2 + (adler + (uint64)(uint32)buf[12]))) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 12) + 1) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 12) + 1, (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 12) + 1);
   };
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 12) + 1) by simp() using {
    adler == at(byte_12, adler + (uint64)(uint32)buf[12]);
    at(byte_12, to_integer(adler + (uint64)(uint32)buf[12])) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 12) + 1);
   };
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 12) + 1) by simp() using {
    sum2 == at(byte_12, sum2 + (adler + (uint64)(uint32)buf[12]));
    at(byte_12, to_integer(sum2 + (adler + (uint64)(uint32)buf[12]))) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 12) + 1);
   };
   have to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 13)) by simp();
   have to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 13)) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 13), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 13)) by simp();
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 13)) by simp();
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 13)) by simp();
   execute_until(assignment(adler, 35));
   apply(zlib_block_read_bound(at(loop(3).entry, len), at(before_block, len), 13u64));
   apply(zlib_full_stream_tail_read_bound(old(len), at(before_block, len), 13u64));
   apply(zlib_block_lane(at(loop(3).entry, buf), at(loop(3).entry, len), at(before_block, len), 13));
   have buf[13] == at(loop(3).entry, buf)[(zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 13)] by simp() using {
    buf == at(loop(3).entry, buf) + (at(loop(3).entry, len) - at(before_block, len));
    (at(loop(3).entry, buf) + (at(loop(3).entry, len) - at(before_block, len)))[13] == at(loop(3).entry, buf)[zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 13];
   };
   apply(zlib_seeded_component_step(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 13), adler, sum2, buf[13], at(loop(3).entry, adler), at(loop(3).entry, sum2)));
   mark byte_13;
   step();
   execute_until(assignment(sum2, 35));
   step();
   have adler == at(byte_13, adler + (uint64)(uint32)buf[13]) by simp();
   have sum2 == at(byte_13, sum2 + (adler + (uint64)(uint32)buf[13])) by simp();
   have to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 13) + 1) by simp() using {
    adler == at(byte_13, adler + (uint64)(uint32)buf[13]);
    at(byte_13, to_integer(adler + (uint64)(uint32)buf[13])) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 13) + 1);
   };
   have to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 13) + 1) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 13) + 1, (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 13) + 1) by simp() using {
    sum2 == at(byte_13, sum2 + (adler + (uint64)(uint32)buf[13]));
    at(byte_13, to_integer(sum2 + (adler + (uint64)(uint32)buf[13]))) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 13) + 1) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 13) + 1, (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 13) + 1);
   };
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 13) + 1) by simp() using {
    adler == at(byte_13, adler + (uint64)(uint32)buf[13]);
    at(byte_13, to_integer(adler + (uint64)(uint32)buf[13])) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 13) + 1);
   };
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 13) + 1) by simp() using {
    sum2 == at(byte_13, sum2 + (adler + (uint64)(uint32)buf[13]));
    at(byte_13, to_integer(sum2 + (adler + (uint64)(uint32)buf[13]))) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 13) + 1);
   };
   have to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 14)) by simp();
   have to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 14)) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 14), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 14)) by simp();
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 14)) by simp();
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 14)) by simp();
   execute_until(assignment(adler, 36));
   apply(zlib_block_read_bound(at(loop(3).entry, len), at(before_block, len), 14u64));
   apply(zlib_full_stream_tail_read_bound(old(len), at(before_block, len), 14u64));
   apply(zlib_block_lane(at(loop(3).entry, buf), at(loop(3).entry, len), at(before_block, len), 14));
   have buf[14] == at(loop(3).entry, buf)[(zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 14)] by simp() using {
    buf == at(loop(3).entry, buf) + (at(loop(3).entry, len) - at(before_block, len));
    (at(loop(3).entry, buf) + (at(loop(3).entry, len) - at(before_block, len)))[14] == at(loop(3).entry, buf)[zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 14];
   };
   apply(zlib_seeded_component_step(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 14), adler, sum2, buf[14], at(loop(3).entry, adler), at(loop(3).entry, sum2)));
   mark byte_14;
   step();
   execute_until(assignment(sum2, 36));
   step();
   have adler == at(byte_14, adler + (uint64)(uint32)buf[14]) by simp();
   have sum2 == at(byte_14, sum2 + (adler + (uint64)(uint32)buf[14])) by simp();
   have to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 14) + 1) by simp() using {
    adler == at(byte_14, adler + (uint64)(uint32)buf[14]);
    at(byte_14, to_integer(adler + (uint64)(uint32)buf[14])) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 14) + 1);
   };
   have to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 14) + 1) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 14) + 1, (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 14) + 1) by simp() using {
    sum2 == at(byte_14, sum2 + (adler + (uint64)(uint32)buf[14]));
    at(byte_14, to_integer(sum2 + (adler + (uint64)(uint32)buf[14]))) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 14) + 1) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 14) + 1, (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 14) + 1);
   };
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 14) + 1) by simp() using {
    adler == at(byte_14, adler + (uint64)(uint32)buf[14]);
    at(byte_14, to_integer(adler + (uint64)(uint32)buf[14])) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 14) + 1);
   };
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 14) + 1) by simp() using {
    sum2 == at(byte_14, sum2 + (adler + (uint64)(uint32)buf[14]));
    at(byte_14, to_integer(sum2 + (adler + (uint64)(uint32)buf[14]))) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 14) + 1);
   };
   have to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 15)) by simp();
   have to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 15)) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 15), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 15)) by simp();
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 15)) by simp();
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 15)) by simp();
   execute_until(assignment(adler, 37));
   apply(zlib_block_read_bound(at(loop(3).entry, len), at(before_block, len), 15u64));
   apply(zlib_full_stream_tail_read_bound(old(len), at(before_block, len), 15u64));
   apply(zlib_block_lane(at(loop(3).entry, buf), at(loop(3).entry, len), at(before_block, len), 15));
   have buf[15] == at(loop(3).entry, buf)[(zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 15)] by simp() using {
    buf == at(loop(3).entry, buf) + (at(loop(3).entry, len) - at(before_block, len));
    (at(loop(3).entry, buf) + (at(loop(3).entry, len) - at(before_block, len)))[15] == at(loop(3).entry, buf)[zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 15];
   };
   apply(zlib_seeded_component_step(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 15), adler, sum2, buf[15], at(loop(3).entry, adler), at(loop(3).entry, sum2)));
   mark byte_15;
   step();
   execute_until(assignment(sum2, 37));
   step();
   have adler == at(byte_15, adler + (uint64)(uint32)buf[15]) by simp();
   have sum2 == at(byte_15, sum2 + (adler + (uint64)(uint32)buf[15])) by simp();
   have to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 15) + 1) by simp() using {
    adler == at(byte_15, adler + (uint64)(uint32)buf[15]);
    at(byte_15, to_integer(adler + (uint64)(uint32)buf[15])) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 15) + 1);
   };
   have to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 15) + 1) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 15) + 1, (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 15) + 1) by simp() using {
    sum2 == at(byte_15, sum2 + (adler + (uint64)(uint32)buf[15]));
    at(byte_15, to_integer(sum2 + (adler + (uint64)(uint32)buf[15]))) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 15) + 1) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 15) + 1, (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 15) + 1);
   };
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 15) + 1) by simp() using {
    adler == at(byte_15, adler + (uint64)(uint32)buf[15]);
    at(byte_15, to_integer(adler + (uint64)(uint32)buf[15])) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 15) + 1);
   };
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 15) + 1) by simp() using {
    sum2 == at(byte_15, sum2 + (adler + (uint64)(uint32)buf[15]));
    at(byte_15, to_integer(sum2 + (adler + (uint64)(uint32)buf[15]))) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 15) + 1);
   };
   have to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 16)) by simp();
   have to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 16)) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 16), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 16)) by simp();
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 16)) by simp();
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 16)) by simp();
   execute_until(back_edge());
   have len <= at(loop(3).entry, len) by simp();
   have at(loop(3).entry, len) - len <= 5551u64 by simp();
   have to_integer(len) <= 5551 by arithmetic() using { to_integer(len) == at(before_block, to_integer(len)) - 16; at(before_block, to_integer(len)) <= 5551; };
   apply(uint64_to_integer_bounds(len));
   apply(uint64_to_integer_less_equal_implies_less_equal(len, 5551u64));
   have len <= 9223372036854775807u64 by arithmetic() using { len <= 5551u64; };
   have to_integer(len) < at(before_block, to_integer(len)) by arithmetic() using { to_integer(len) == at(before_block, to_integer(len)) - 16; };
   have to_integer(zlib_prefix_count(at(loop(3).entry, len), len)) == to_integer(zlib_prefix_count(at(loop(3).entry, len), at(before_block, len))) + 16 by simp();
   have defined(zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 16) by simp();
   apply(int32_add_to_integer(zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)), 16));
   have to_integer(zlib_prefix_count(at(loop(3).entry, len), len)) == to_integer(zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 16) by arithmetic() using {
    to_integer(zlib_prefix_count(at(loop(3).entry, len), len)) == to_integer(zlib_prefix_count(at(loop(3).entry, len), at(before_block, len))) + 16;
    to_integer(zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 16) == to_integer(zlib_prefix_count(at(loop(3).entry, len), at(before_block, len))) + to_integer(16);
   };
   apply(int32_to_integer_equal_implies_equal(zlib_prefix_count(at(loop(3).entry, len), len), zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 16));
   have buf == at(before_block, buf) + 16 by simp();
   have at(loop(3).entry, len) - len == (at(loop(3).entry, len) - at(before_block, len)) + 16u64 by arithmetic() using {
    len == at(before_block, len - 16u64);
    16u64 <= at(before_block, len);
    at(before_block, len) <= at(loop(3).entry, len);
    at(loop(3).entry, len) <= 5551u64;
   };
   have buf == at(loop(3).entry, buf) + (at(loop(3).entry, len) - len) by {
    rewrite(buf == at(before_block, buf) + 16);
    rewrite(at(loop(3).entry, len) - len == (at(loop(3).entry, len) - at(before_block, len)) + 16u64);
    arithmetic_certificate rules {
     premise 0: at(before_block, buf) == at(loop(3).entry, buf) + (at(loop(3).entry, len) - at(before_block, len)) => at(before_block, buf) == at(loop(3).entry, buf) + (at(loop(3).entry, len) - at(before_block, len));
     premise 1: at(loop(3).entry, len) - at(before_block, len) <= 5535u64 => at(loop(3).entry, len) - at(before_block, len) <= 5535u64;
     pointer_translation relation 0 bounds [1] => at(before_block, buf) + 16 == at(loop(3).entry, buf) + ((at(loop(3).entry, len) - at(before_block, len)) + 16u64);
     conclusion 0;
    }
   }
   have len <= at(before_block, len) - 16u64 by simp();
   have viewable(buf[0u64..len]) by {
    transport(at(before_block, viewable(buf[0u64..len])), viewable(buf[0u64..len])) using {
     buf == at(before_block, buf) + 16;
     at(before_block, viewable(buf[0u64..len]));
     16u64 <= at(before_block, len);
     len <= at(before_block, len) - 16u64;
     len <= 5551u64;
     len <= 9223372036854775807u64;
    };
   }
   have to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), zlib_prefix_count(at(loop(3).entry, len), len)) by { rewrite(zlib_prefix_count(at(loop(3).entry, len), len) == zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 16); assumption(); }
   have to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer(zlib_prefix_count(at(loop(3).entry, len), len)) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), zlib_prefix_count(at(loop(3).entry, len), len), zlib_prefix_count(at(loop(3).entry, len), len)) by { rewrite(zlib_prefix_count(at(loop(3).entry, len), len) == zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 16); assumption(); }
   have to_integer(adler) <= 65520 + 255 * to_integer(zlib_prefix_count(at(loop(3).entry, len), len)) by { rewrite(zlib_prefix_count(at(loop(3).entry, len), len) == zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 16); assumption(); }
   have to_integer(sum2) <= 65520 + 1481280 * to_integer(zlib_prefix_count(at(loop(3).entry, len), len)) by { rewrite(zlib_prefix_count(at(loop(3).entry, len), len) == zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 16); assumption(); }
   have len <= old(len) by arithmetic() using {
    len == at(before_block, len) - 16u64;
    16u64 <= at(before_block, len); at(before_block, len) <= old(len); old(len) <= 2147483647u64;
   };
   have old(len) - at(before_block, len) <= 2147483647u64 by arithmetic() using {
    at(before_block, len) <= old(len); old(len) <= 2147483647u64;
   };
   apply(zlib_full_stream_prefix_step(old(len), at(before_block, len), 16u64));
   apply(zlib_full_prefix_observation(old(len), at(before_block, len)));
   apply(zlib_full_prefix_pointer(old(buf), old(len), at(before_block, len)));
   have old(len) - len <= 2147483647u64 by arithmetic() using { len <= old(len); old(len) <= 2147483647u64; };
   apply(zlib_full_prefix_pointer(old(buf), old(len), len));
   have zlib_prefix_count(old(len), len) == zlib_prefix_count(old(len), at(before_block, len)) + 16 by simp() using {
    len == at(before_block, len) - 16u64;
    zlib_prefix_count(old(len), at(before_block, len) - 16u64) == zlib_prefix_count(old(len), at(before_block, len)) + (int32)(uint32)16u64;
   };
   apply(zlib_full_chunk_bound(old(len), at(before_block, len), 16u64));
   have defined(zlib_prefix_count(old(len), at(before_block, len)) + 16) by simp();
   have old(buf) + zlib_prefix_count(old(len), at(before_block, len)) + 16 == old(buf) + (zlib_prefix_count(old(len), at(before_block, len)) + 16) by normalize() using { defined(zlib_prefix_count(old(len), at(before_block, len)) + 16); };
   have buf == old(buf) + (old(len) - len) by simp() using {
    buf == at(before_block, buf) + 16;
    at(before_block, buf) == old(buf) + (old(len) - at(before_block, len));
    old(buf) + (old(len) - at(before_block, len)) == old(buf) + zlib_prefix_count(old(len), at(before_block, len));
    old(buf) + zlib_prefix_count(old(len), at(before_block, len)) + 16 == old(buf) + (zlib_prefix_count(old(len), at(before_block, len)) + 16);
    zlib_prefix_count(old(len), len) == zlib_prefix_count(old(len), at(before_block, len)) + 16;
    old(buf) + (old(len) - len) == old(buf) + zlib_prefix_count(old(len), len);
   };
   close_invariants() by assumption();
  }
 }
 have len <= 15u64 by arithmetic() using { not (len >= 16u64); len <= at(loop(3).entry, len); at(loop(3).entry, len) <= 5551u64; };
 apply(uint64_less_equal_to_integer(len, 15u64));
  // The original C performs no MOD between the DO16 and scalar tail loops.
  execute_until(loop(4));
  have old(len) - at(loop(3).entry, len) <= 2147483647u64 by arithmetic() using { at(loop(3).entry, len) <= old(len); old(len) <= 2147483647u64; };
  have at(loop(3).entry, len) - len <= 2147483647u64 by arithmetic() using { len <= at(loop(3).entry, len); at(loop(3).entry, len) <= 5551u64; };
  apply(zlib_full_prefix_observation(old(len), at(loop(3).entry, len)));
  apply(zlib_full_prefix_observation(at(loop(3).entry, len), len));
  apply(zlib_full_prefix_pointer(old(buf), old(len), at(loop(3).entry, len)));
  have at(loop(3).entry, buf) == old(buf) + zlib_prefix_count(old(len), at(loop(3).entry, len)) by simp();
  apply(zlib_full_concat_bound(old(len), at(loop(3).entry, len), len));
  have defined(zlib_prefix_count(old(len), at(loop(3).entry, len)) + zlib_prefix_count(at(loop(3).entry, len), len)) by simp();
  have to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(old(buf) + zlib_prefix_count(old(len), at(loop(3).entry, len)), zlib_prefix_count(at(loop(3).entry, len), len)) by { rewrite(old(buf) + zlib_prefix_count(old(len), at(loop(3).entry, len)) == at(loop(3).entry, buf)); assumption(); }
  have to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer(zlib_prefix_count(at(loop(3).entry, len), len)) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(old(buf) + zlib_prefix_count(old(len), at(loop(3).entry, len)), zlib_prefix_count(at(loop(3).entry, len), len), zlib_prefix_count(at(loop(3).entry, len), len)) by { rewrite(old(buf) + zlib_prefix_count(old(len), at(loop(3).entry, len)) == at(loop(3).entry, buf)); assumption(); }
  apply(zlib_seeded_batch_concat(old(buf), zlib_prefix_count(old(len), at(loop(3).entry, len)), zlib_prefix_count(at(loop(3).entry, len), len), adler, sum2, at(loop(3).entry, adler), at(loop(3).entry, sum2)));
  apply(zlib_full_stream_split_count(old(len), at(loop(3).entry, len), len));
  have to_integer(adler % 65521u64) == adler_spec_a(old(buf), zlib_prefix_count(old(len), len), 1) by { rewrite(zlib_prefix_count(old(len), len) == zlib_prefix_count(old(len), at(loop(3).entry, len)) + zlib_prefix_count(at(loop(3).entry, len), len)); assumption(); }
  have to_integer(sum2 % 65521u64) == adler_spec_b(old(buf), zlib_prefix_count(old(len), len), 1, 0) by { rewrite(zlib_prefix_count(old(len), len) == zlib_prefix_count(old(len), at(loop(3).entry, len)) + zlib_prefix_count(at(loop(3).entry, len), len)); assumption(); }
  apply(int32_less_equal_to_integer(zlib_prefix_count(at(loop(3).entry, len), len), 2147483647));
  apply(uint64_less_equal_to_integer(at(loop(3).entry, len) - len, 5551u64));
  have to_integer(zlib_prefix_count(at(loop(3).entry, len), len)) <= to_integer(5551) by arithmetic() using { to_integer(zlib_prefix_count(at(loop(3).entry, len), len)) == to_integer(at(loop(3).entry, len) - len); to_integer(at(loop(3).entry, len) - len) <= to_integer(5551u64); };
  apply(int32_to_integer_less_equal_implies_less_equal(zlib_prefix_count(at(loop(3).entry, len), len), 5551));
  apply(int32_less_equal_to_integer(zlib_prefix_count(at(loop(3).entry, len), len), 5551));
  have to_integer(adler) <= 1500000 by arithmetic() using { to_integer(adler) <= 65520 + 255 * to_integer(zlib_prefix_count(at(loop(3).entry, len), len)); to_integer(zlib_prefix_count(at(loop(3).entry, len), len)) <= 5551; };
  have to_integer(sum2) <= 10000000000 by arithmetic() using { to_integer(sum2) <= 65520 + 1481280 * to_integer(zlib_prefix_count(at(loop(3).entry, len), len)); to_integer(zlib_prefix_count(at(loop(3).entry, len), len)) <= 5551; };
  apply(uint64_to_integer_less_equal_implies_less_equal(adler, 1500000u64));
  apply(uint64_to_integer_less_equal_implies_less_equal(sum2, 10000000000u64));
  loop {
   decreases to_integer(len);
   invariant len <= at(loop(4).entry, len);
   invariant at(loop(4).entry, len) <= 15u64;
   invariant at(loop(4).entry, len) <= old(len);
   invariant old(len) <= 2147483647u64;
   invariant len <= old(len);
   invariant buf == at(loop(4).entry, buf) + (at(loop(4).entry, len) - len);
   invariant buf == old(buf) + (old(len) - len);
   invariant at(loop(4).entry, buf) == old(buf) + (old(len) - at(loop(4).entry, len));
   invariant viewable(buf[0u64..len]);
   invariant at(loop(4).entry, adler) <= 1500000u64;
   invariant at(loop(4).entry, sum2) <= 10000000000u64;
   invariant to_integer(at(loop(4).entry, adler) % 65521u64) == adler_spec_a(old(buf), zlib_prefix_count(old(len), at(loop(4).entry, len)), 1);
   invariant to_integer(at(loop(4).entry, sum2) % 65521u64) == adler_spec_b(old(buf), zlib_prefix_count(old(len), at(loop(4).entry, len)), 1, 0);
   invariant to_integer(adler) == to_integer(at(loop(4).entry, adler)) + adler_byte_sum(at(loop(4).entry, buf), zlib_prefix_count(at(loop(4).entry, len), len));
   invariant to_integer(sum2) == to_integer(at(loop(4).entry, sum2)) + to_integer(zlib_prefix_count(at(loop(4).entry, len), len)) * to_integer(at(loop(4).entry, adler)) + adler_weighted_sum(at(loop(4).entry, buf), zlib_prefix_count(at(loop(4).entry, len), len), zlib_prefix_count(at(loop(4).entry, len), len));
   invariant to_integer(adler) <= 1500000 + 255 * to_integer(zlib_prefix_count(at(loop(4).entry, len), len));
   invariant to_integer(sum2) <= 10000000000 + 1504080 * to_integer(zlib_prefix_count(at(loop(4).entry, len), len));
   initialize by {
    have len <= 9223372036854775807u64 by arithmetic() using { len <= 15u64; };
    have zlib_prefix_count(at(loop(4).entry, len), len) == 0 by { unfold(zlib_prefix_count(at(loop(4).entry, len), len)); simp(); }
    apply(adler_sum_empty(at(loop(4).entry, buf), 0));
    apply(uint64_less_equal_to_integer(adler, 1500000u64));
    apply(uint64_less_equal_to_integer(sum2, 10000000000u64));
    have to_integer(adler) == to_integer(at(loop(4).entry, adler)) + adler_byte_sum(at(loop(4).entry, buf), zlib_prefix_count(at(loop(4).entry, len), len)) by { rewrite(zlib_prefix_count(at(loop(4).entry, len), len) == 0); arithmetic() using { adler_byte_sum(at(loop(4).entry, buf), 0) == 0; }; }
    have to_integer(sum2) == to_integer(at(loop(4).entry, sum2)) + to_integer(zlib_prefix_count(at(loop(4).entry, len), len)) * to_integer(at(loop(4).entry, adler)) + adler_weighted_sum(at(loop(4).entry, buf), zlib_prefix_count(at(loop(4).entry, len), len), zlib_prefix_count(at(loop(4).entry, len), len)) by { rewrite(zlib_prefix_count(at(loop(4).entry, len), len) == 0); arithmetic() using { adler_weighted_sum(at(loop(4).entry, buf), 0, 0) == 0; }; }
    have to_integer(adler) <= 1500000 + 255 * to_integer(zlib_prefix_count(at(loop(4).entry, len), len)) by { rewrite(zlib_prefix_count(at(loop(4).entry, len), len) == 0); arithmetic() using { to_integer(adler) <= 1500000; }; }
    have to_integer(sum2) <= 10000000000 + 1504080 * to_integer(zlib_prefix_count(at(loop(4).entry, len), len)) by { rewrite(zlib_prefix_count(at(loop(4).entry, len), len) == 0); arithmetic() using { to_integer(sum2) <= 10000000000; }; }
    simp();
   }
   preserve by {
    if len == 0u64 {
     // Record the checksum before the zero guard decrements len to UINT64_MAX.
     have old(len) - at(loop(4).entry, len) <= 2147483647u64 by arithmetic() using { at(loop(4).entry, len) <= old(len); old(len) <= 2147483647u64; };
     have at(loop(4).entry, len) - len <= 2147483647u64 by arithmetic() using { len <= at(loop(4).entry, len); at(loop(4).entry, len) <= 15u64; };
     apply(zlib_full_prefix_observation(old(len), at(loop(4).entry, len))); apply(zlib_full_prefix_observation(at(loop(4).entry, len), len));
     apply(zlib_full_prefix_pointer(old(buf), old(len), at(loop(4).entry, len)));
     have at(loop(4).entry, buf) == old(buf) + zlib_prefix_count(old(len), at(loop(4).entry, len)) by simp();
     apply(zlib_full_concat_bound(old(len), at(loop(4).entry, len), len));
     have defined(zlib_prefix_count(old(len), at(loop(4).entry, len)) + zlib_prefix_count(at(loop(4).entry, len), len)) by simp();
     have to_integer(adler) == to_integer(at(loop(4).entry, adler)) + adler_byte_sum(old(buf) + zlib_prefix_count(old(len), at(loop(4).entry, len)), zlib_prefix_count(at(loop(4).entry, len), len)) by { rewrite(old(buf) + zlib_prefix_count(old(len), at(loop(4).entry, len)) == at(loop(4).entry, buf)); assumption(); }
  have to_integer(sum2) == to_integer(at(loop(4).entry, sum2)) + to_integer(zlib_prefix_count(at(loop(4).entry, len), len)) * to_integer(at(loop(4).entry, adler)) + adler_weighted_sum(old(buf) + zlib_prefix_count(old(len), at(loop(4).entry, len)), zlib_prefix_count(at(loop(4).entry, len), len), zlib_prefix_count(at(loop(4).entry, len), len)) by { rewrite(old(buf) + zlib_prefix_count(old(len), at(loop(4).entry, len)) == at(loop(4).entry, buf)); assumption(); }
  apply(zlib_raw_seeded_batch_concat(old(buf), zlib_prefix_count(old(len), at(loop(4).entry, len)), zlib_prefix_count(at(loop(4).entry, len), len), adler, sum2, at(loop(4).entry, adler), at(loop(4).entry, sum2)));
     apply(zlib_full_stream_split_count(old(len), at(loop(4).entry, len), len));
     have zlib_prefix_count(old(len), len) == old((int32)(uint32)len) by { unfold(zlib_prefix_count(old(len), len)); simp(); }
     have to_integer(adler % 65521u64) == adler_spec_a(old(buf), zlib_prefix_count(old(len), len), 1) by { rewrite(zlib_prefix_count(old(len), len) == zlib_prefix_count(old(len), at(loop(4).entry, len)) + zlib_prefix_count(at(loop(4).entry, len), len)); assumption(); }
     have to_integer(adler % 65521u64) == adler_spec_a(old(buf), old((int32)(uint32)len), 1) by { rewrite(old((int32)(uint32)len) == zlib_prefix_count(old(len), len)); assumption(); }
     have to_integer(sum2 % 65521u64) == adler_spec_b(old(buf), zlib_prefix_count(old(len), len), 1, 0) by { rewrite(zlib_prefix_count(old(len), len) == zlib_prefix_count(old(len), at(loop(4).entry, len)) + zlib_prefix_count(at(loop(4).entry, len), len)); assumption(); }
     have to_integer(sum2 % 65521u64) == adler_spec_b(old(buf), old((int32)(uint32)len), 1, 0) by { rewrite(old((int32)(uint32)len) == zlib_prefix_count(old(len), len)); assumption(); }
     apply(zlib_components_pack(old(buf), old((int32)(uint32)len), adler, sum2));
     step(); step(); step(); step();
     have __click_call_result4 == 0u64 by assumption(); step();
    } else {
     have 0u64 <= len by normalize();
     have 0u64 < len by {
      if 0u64 < len { assumption(); } else {
       apply(uint64_less_equal_and_not_less_than_implies_equal(0u64, len));
       have len == 0u64 by { rewrite(0u64 == len); normalize(); }
       contradiction(len == 0u64);
      }
     }
     apply(uint64_less_than_to_integer(0u64, len));
     have to_integer(1u64) <= to_integer(len) by arithmetic() using { to_integer(0u64) < to_integer(len); };
     apply(uint64_to_integer_less_equal_implies_less_equal(1u64, len));
     have len <= 15u64 by arithmetic() using { len <= at(loop(4).entry, len); at(loop(4).entry, len) <= 15u64; };
     apply(uint64_subtract_to_integer(len, 1u64));
     have at(loop(4).entry, len) <= 2147483647u64 by arithmetic() using { at(loop(4).entry, len) <= 15u64; };
     apply(zlib_full_stream_remaining_step(at(loop(4).entry, len), len, 1u64));
     apply(zlib_full_stream_prefix_step(at(loop(4).entry, len), len, 1u64));
     apply(zlib_full_stream_prefix_step(old(len), len, 1u64));
     have at(loop(4).entry, len) - len <= 2147483647u64 by arithmetic() using { len <= at(loop(4).entry, len); at(loop(4).entry, len) <= 15u64; };
     apply(zlib_full_prefix_observation(at(loop(4).entry, len), len));
     have at(loop(4).entry, len) - len <= 15u64 by arithmetic() using { len <= at(loop(4).entry, len); at(loop(4).entry, len) <= 15u64; };
     apply(uint64_less_equal_to_integer(at(loop(4).entry, len) - len, 15u64));
     have to_integer(zlib_prefix_count(at(loop(4).entry, len), len)) <= to_integer(15) by arithmetic() using { to_integer(zlib_prefix_count(at(loop(4).entry, len), len)) == to_integer(at(loop(4).entry, len) - len); to_integer(at(loop(4).entry, len) - len) <= to_integer(15u64); };
     apply(int32_to_integer_less_equal_implies_less_equal(zlib_prefix_count(at(loop(4).entry, len), len), 15));
     have 15 < 16 by normalize();
     apply(int32_less_equal_less_than_transitive(zlib_prefix_count(at(loop(4).entry, len), len), 15, 16));
     have viewable(buf[0u64..1u64]) by simp();
     mark before_decrement;
     step(); step(); step(); step(); step();
     have len == at(before_decrement, len) - 1u64 by simp();
     have to_integer(len) == at(before_decrement, to_integer(len)) - 1 by assumption();
     execute_until(assignment(adler, 38));
     have __click_call_result3 == at(before_decrement, buf) by simp();
     apply(zlib_full_stream_scalar_read_bound(old(len), at(before_decrement, len)));
     have at(loop(4).entry, len) - at(before_decrement, len) <= 2147483647u64 by arithmetic() using { at(before_decrement, len) <= at(loop(4).entry, len); at(loop(4).entry, len) <= 15u64; };
     apply(zlib_full_prefix_pointer(at(loop(4).entry, buf), at(loop(4).entry, len), at(before_decrement, len)));
     have __click_call_result3[0] == at(loop(4).entry, buf)[zlib_prefix_count(at(loop(4).entry, len), at(before_decrement, len))] by simp() using {
      __click_call_result3 == at(before_decrement, buf);
      at(before_decrement, buf) == at(loop(4).entry, buf) + (at(loop(4).entry, len) - at(before_decrement, len));
      at(loop(4).entry, buf) + (at(loop(4).entry, len) - at(before_decrement, len)) == at(loop(4).entry, buf) + zlib_prefix_count(at(loop(4).entry, len), at(before_decrement, len));
     };
     apply(zlib_scalar_seeded_component_step(at(loop(4).entry, buf), zlib_prefix_count(at(loop(4).entry, len), at(before_decrement, len)), adler, sum2, __click_call_result3[0], at(loop(4).entry, adler), at(loop(4).entry, sum2)));
     mark before_add;
     step(); execute_until(assignment(sum2, 38)); step();
     have adler == at(before_add, adler + (uint64)(uint32)__click_call_result3[0]) by simp();
     have sum2 == at(before_add, sum2 + (adler + (uint64)(uint32)__click_call_result3[0])) by simp();
     have zlib_prefix_count(at(loop(4).entry, len), len) == zlib_prefix_count(at(loop(4).entry, len), at(before_decrement, len)) + 1 by simp();
     have to_integer(adler) == to_integer(at(loop(4).entry, adler)) + adler_byte_sum(at(loop(4).entry, buf), zlib_prefix_count(at(loop(4).entry, len), len)) by simp() using { zlib_prefix_count(at(loop(4).entry, len), len) == zlib_prefix_count(at(loop(4).entry, len), at(before_decrement, len)) + 1; adler == at(before_add, adler + (uint64)(uint32)__click_call_result3[0]); sum2 == at(before_add, sum2 + (adler + (uint64)(uint32)__click_call_result3[0])); at(before_add, to_integer(adler + (uint64)(uint32)__click_call_result3[0]) == to_integer(at(loop(4).entry, adler)) + adler_byte_sum(at(loop(4).entry, buf), (zlib_prefix_count(at(loop(4).entry, len), at(before_decrement, len)) + 1))); };
     have to_integer(sum2) == to_integer(at(loop(4).entry, sum2)) + to_integer(zlib_prefix_count(at(loop(4).entry, len), len)) * to_integer(at(loop(4).entry, adler)) + adler_weighted_sum(at(loop(4).entry, buf), zlib_prefix_count(at(loop(4).entry, len), len), zlib_prefix_count(at(loop(4).entry, len), len)) by simp() using { zlib_prefix_count(at(loop(4).entry, len), len) == zlib_prefix_count(at(loop(4).entry, len), at(before_decrement, len)) + 1; adler == at(before_add, adler + (uint64)(uint32)__click_call_result3[0]); sum2 == at(before_add, sum2 + (adler + (uint64)(uint32)__click_call_result3[0])); at(before_add, to_integer(sum2 + (adler + (uint64)(uint32)__click_call_result3[0])) == to_integer(at(loop(4).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(4).entry, len), at(before_decrement, len)) + 1)) * to_integer(at(loop(4).entry, adler)) + adler_weighted_sum(at(loop(4).entry, buf), (zlib_prefix_count(at(loop(4).entry, len), at(before_decrement, len)) + 1), (zlib_prefix_count(at(loop(4).entry, len), at(before_decrement, len)) + 1))); };
     have to_integer(adler) <= 1500000 + 255 * to_integer(zlib_prefix_count(at(loop(4).entry, len), len)) by simp() using { zlib_prefix_count(at(loop(4).entry, len), len) == zlib_prefix_count(at(loop(4).entry, len), at(before_decrement, len)) + 1; adler == at(before_add, adler + (uint64)(uint32)__click_call_result3[0]); sum2 == at(before_add, sum2 + (adler + (uint64)(uint32)__click_call_result3[0])); at(before_add, to_integer(adler + (uint64)(uint32)__click_call_result3[0]) <= 1500000 + 255 * to_integer((zlib_prefix_count(at(loop(4).entry, len), at(before_decrement, len)) + 1))); };
     have to_integer(sum2) <= 10000000000 + 1504080 * to_integer(zlib_prefix_count(at(loop(4).entry, len), len)) by simp() using { zlib_prefix_count(at(loop(4).entry, len), len) == zlib_prefix_count(at(loop(4).entry, len), at(before_decrement, len)) + 1; adler == at(before_add, adler + (uint64)(uint32)__click_call_result3[0]); sum2 == at(before_add, sum2 + (adler + (uint64)(uint32)__click_call_result3[0])); at(before_add, to_integer(sum2 + (adler + (uint64)(uint32)__click_call_result3[0])) <= 10000000000 + 1504080 * to_integer((zlib_prefix_count(at(loop(4).entry, len), at(before_decrement, len)) + 1))); };
     have len <= at(before_decrement, len) by arithmetic() using { len == at(before_decrement, len) - 1u64; 1u64 <= at(before_decrement, len); at(before_decrement, len) <= 15u64; };
     have len <= at(loop(4).entry, len) by arithmetic() using { len <= at(before_decrement, len); at(before_decrement, len) <= at(loop(4).entry, len); at(loop(4).entry, len) <= 2147483647u64; };
     have at(loop(4).entry, len) - at(before_decrement, len) <= 2147483647u64 by arithmetic() using { at(before_decrement, len) <= at(loop(4).entry, len); at(loop(4).entry, len) <= 2147483647u64; };
     have at(loop(4).entry, len) - len <= 2147483647u64 by arithmetic() using { len <= at(loop(4).entry, len); at(loop(4).entry, len) <= 2147483647u64; };
     apply(zlib_full_prefix_pointer(at(loop(4).entry, buf), at(loop(4).entry, len), at(before_decrement, len))); apply(zlib_full_prefix_pointer(at(loop(4).entry, buf), at(loop(4).entry, len), len));
     have zlib_prefix_count(at(loop(4).entry, len), len) == zlib_prefix_count(at(loop(4).entry, len), at(before_decrement, len)) + 1 by simp();
     have defined(zlib_prefix_count(at(loop(4).entry, len), at(before_decrement, len)) + 1) by simp();
     have at(loop(4).entry, buf) + zlib_prefix_count(at(loop(4).entry, len), at(before_decrement, len)) + 1 == at(loop(4).entry, buf) + (zlib_prefix_count(at(loop(4).entry, len), at(before_decrement, len)) + 1) by normalize() using { defined(zlib_prefix_count(at(loop(4).entry, len), at(before_decrement, len)) + 1); };
     have buf == at(loop(4).entry, buf) + (at(loop(4).entry, len) - len) by simp() using {
      buf == at(before_decrement, buf) + 1;
      at(before_decrement, buf) == at(loop(4).entry, buf) + (at(loop(4).entry, len) - at(before_decrement, len));
      at(loop(4).entry, buf) + (at(loop(4).entry, len) - at(before_decrement, len)) == at(loop(4).entry, buf) + zlib_prefix_count(at(loop(4).entry, len), at(before_decrement, len));
      at(loop(4).entry, buf) + zlib_prefix_count(at(loop(4).entry, len), at(before_decrement, len)) + 1 == at(loop(4).entry, buf) + (zlib_prefix_count(at(loop(4).entry, len), at(before_decrement, len)) + 1);
      zlib_prefix_count(at(loop(4).entry, len), len) == zlib_prefix_count(at(loop(4).entry, len), at(before_decrement, len)) + 1;
      at(loop(4).entry, buf) + (at(loop(4).entry, len) - len) == at(loop(4).entry, buf) + zlib_prefix_count(at(loop(4).entry, len), len);
     };
     have len <= old(len) by arithmetic() using { len <= at(before_decrement, len); at(before_decrement, len) <= old(len); old(len) <= 2147483647u64; };
     have old(len) - at(before_decrement, len) <= 2147483647u64 by arithmetic() using { at(before_decrement, len) <= old(len); old(len) <= 2147483647u64; };
     have old(len) - len <= 2147483647u64 by arithmetic() using { len <= old(len); old(len) <= 2147483647u64; };
     apply(zlib_full_prefix_observation(old(len), at(before_decrement, len)));
     apply(zlib_full_prefix_observation(old(len), len));
     apply(zlib_full_prefix_pointer(old(buf), old(len), at(before_decrement, len))); apply(zlib_full_prefix_pointer(old(buf), old(len), len));
     have zlib_prefix_count(old(len), len) == zlib_prefix_count(old(len), at(before_decrement, len)) + 1 by simp();
     apply(zlib_full_chunk_bound(old(len), at(before_decrement, len), 1u64));
     have defined(zlib_prefix_count(old(len), at(before_decrement, len)) + 1) by simp();
     have old(buf) + zlib_prefix_count(old(len), at(before_decrement, len)) + 1 == old(buf) + (zlib_prefix_count(old(len), at(before_decrement, len)) + 1) by normalize() using { defined(zlib_prefix_count(old(len), at(before_decrement, len)) + 1); };
     have buf == old(buf) + (old(len) - len) by simp() using {
      buf == at(before_decrement, buf) + 1;
      at(before_decrement, buf) == old(buf) + (old(len) - at(before_decrement, len));
      old(buf) + (old(len) - at(before_decrement, len)) == old(buf) + zlib_prefix_count(old(len), at(before_decrement, len));
      old(buf) + zlib_prefix_count(old(len), at(before_decrement, len)) + 1 == old(buf) + (zlib_prefix_count(old(len), at(before_decrement, len)) + 1);
      zlib_prefix_count(old(len), len) == zlib_prefix_count(old(len), at(before_decrement, len)) + 1;
      old(buf) + (old(len) - len) == old(buf) + zlib_prefix_count(old(len), len);
     };
     have len <= 9223372036854775807u64 by arithmetic() using { len <= at(loop(4).entry, len); at(loop(4).entry, len) <= 15u64; };
     have viewable(buf[0u64..len]) by {
      transport(at(before_decrement, viewable(buf[0u64..len])), viewable(buf[0u64..len])) using {
       buf == at(before_decrement, buf) + 1;
       at(before_decrement, viewable(buf[0u64..len]));
       1u64 <= at(before_decrement, len); len == at(before_decrement, len) - 1u64;
       len <= 9223372036854775807u64;
      };
     }
     apply(uint64_to_integer_bounds(len));
     have to_integer(len) < at(before_decrement, to_integer(len)) by arithmetic() using { to_integer(len) == at(before_decrement, to_integer(len)) - 1; };
     close_invariants() by assumption();
    }
   }
  }
  execute_until(assignment(adler, 39));
  execute(); simp();
 }

  }
 }
}
