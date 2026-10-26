import click::integer;

target "x86_64-unknown-linux-gnu";
verifying "../../vendor/zlib-1.3.1/adler32.c";
import "byte.click";
import "../adler32-spec-bridge.click";
import "short-prefix.click";
uint64 adler32_z(uint64 adler, const uint8* buf, uint64 len) {
 requires adler == 1u64;
 requires 2u64 <= len;
 requires len <= 15u64;
 requires buf != 0;
 views buf[0u64..len];
 ensures to_integer(result) == adler_spec_checksum_u64(old(buf), old(len), 1, 0);
 ensures result <= 4294967295u64;
 ensures forall (k: uint64) { k < old(len) implies old(buf)[k] == old(buf[k]) };
} by {
 have len <= 2147483647u64 by solve() using { len <= 15u64; };
 have to_integer(len as uint32 as int32) == to_integer(len) by {
  arithmetic_certificate rules {
   premise 0: 0 <= to_integer(len) => 0 <= to_integer(len);
   premise 1: to_integer(len) <= 2147483647 => to_integer(len) <= 2147483647;
   integer_cast_identity bounds [0, 1] => to_integer(len as uint32 as int32) == to_integer(len);
   conclusion 0;
  }
 }
 have viewable(buf[0u64..len]) by solve();
 step_until(loop(0));
 have viewable(buf[0u64..len]) by solve();
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
   have adler == 1u64 by solve();
   have sum2 == 0u64 by solve();
   apply(adler_sum_empty(old(buf), 0));
   have old(len) - len == 0u64 by solve();
   have to_integer(adler) == 1 by { solve() using { adler == 1u64; }; }
   have to_integer(sum2) == 0 by { solve() using { sum2 == 0u64; }; }
   have 1 <= to_integer(adler) by solve() using { to_integer(adler) == 1; };
   have to_integer(adler) <= 3826 by solve() using { to_integer(adler) == 1; };
   have 0 <= to_integer(sum2) by solve() using { to_integer(sum2) == 0; };
   have to_integer(sum2) <= 57390 by solve() using { to_integer(sum2) == 0; };
   have to_integer(old(len)) == to_integer(len) by solve();
   have zlib_prefix_count(old(len), len) == 0 by {
    unfold(zlib_prefix_count(old(len), len));
    solve();
   }
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), zlib_prefix_count(old(len), len)) by {
    rewrite(zlib_prefix_count(old(len), len) == 0);
    rewrite(adler_byte_sum(old(buf), 0) == 0);
    solve() using { to_integer(adler) == 1; };
   }
   have to_integer(sum2) == to_integer(zlib_prefix_count(old(len), len)) + adler_weighted_sum(old(buf), zlib_prefix_count(old(len), len), zlib_prefix_count(old(len), len)) by {
    rewrite(zlib_prefix_count(old(len), len) == 0);
    rewrite(adler_weighted_sum(old(buf), 0, 0) == 0);
    solve() using { to_integer(sum2) == 0; };
   }
   have to_integer(adler) <= 1 + 255 * (to_integer(old(len)) - to_integer(len)) by solve() using { to_integer(adler) == 1; to_integer(old(len)) == to_integer(len); };
   have to_integer(sum2) <= 3826 * (to_integer(old(len)) - to_integer(len)) by solve() using { to_integer(sum2) == 0; to_integer(old(len)) == to_integer(len); };
   solve();
  }
  preserve by {
   if len == 0u64 {
    have old(len) - len == old(len) by solve();
    have zlib_prefix_count(old(len), len) == old(len as uint32 as int32) by {
     unfold(zlib_prefix_count(old(len), len));
     solve();
    }
    have to_integer(adler) == 1 + adler_byte_sum(old(buf), old(len as uint32 as int32)) by {
     solve() using { to_integer(adler) == 1 + adler_byte_sum(old(buf), zlib_prefix_count(old(len), len)); zlib_prefix_count(old(len), len) == old(len as uint32 as int32); };
    }
    have to_integer(sum2) == to_integer(old(len as uint32 as int32)) + adler_weighted_sum(old(buf), old(len as uint32 as int32), old(len as uint32 as int32)) by {
     solve() using { to_integer(sum2) == to_integer(zlib_prefix_count(old(len), len)) + adler_weighted_sum(old(buf), zlib_prefix_count(old(len), len), zlib_prefix_count(old(len), len)); zlib_prefix_count(old(len), len) == old(len as uint32 as int32); };
    }
    step(); step(); step(); step();
    have __click_call_result1 == 0u64 by assumption();
    step();
   } else {
    have 0u64 <= len by normalize();
    have 0u64 < len by {
     if 0u64 < len { assumption(); } else {
      have 0u64 == len;
      have len == 0u64 by { rewrite(0u64 == len); normalize(); }
      contradiction(len == 0u64);
     }
    }
   have to_integer(1u64) <= to_integer(len) by solve() using { to_integer(0u64) < to_integer(len); };
   have to_integer(len - 1u64) == to_integer(len) - to_integer(1u64);
   step(); step();
   have 0u64 < len by assumption();
   have 0u64 <= len by normalize();
   have 0u64 <= len - 0u64 by normalize();
   have viewable(buf[0u64..1u64]) by solve();
   have viewable(buf[0u64..len]) by solve();
   mark before_decrement;
   step(); step(); step();
   have to_integer(len) == at(before_decrement, to_integer(len)) - 1 by assumption();
   have to_integer(len) <= 15 by solve() using { to_integer(len) == at(before_decrement, to_integer(len)) - 1; at(before_decrement, to_integer(len)) <= 15; };
   have 0 <= to_integer(len) by solve() using { to_integer(len) == at(before_decrement, to_integer(len)) - 1; to_integer(1u64) <= at(before_decrement, to_integer(len)); };
   have to_integer(len) < at(before_decrement, to_integer(len)) by solve() using { to_integer(len) == at(before_decrement, to_integer(len)) - 1; };
   step_until(assignment(adler, 3));
   have __click_call_result0 == at(before_decrement, buf) by solve();
   have viewable(__click_call_result0[0u64..1u64]) by {
    solve() using { __click_call_result0 == at(before_decrement, buf); at(before_decrement, viewable(buf[0u64..1u64])); };
   }
   have __click_call_result0 == old(buf) + (old(len) - at(before_decrement, len)) by solve();
   have at(before_decrement, len) <= old(len) by assumption();
   have to_integer(old(len) - at(before_decrement, len)) == to_integer(old(len)) - to_integer(at(before_decrement, len));
   have to_integer(old(len) - at(before_decrement, len)) < to_integer(old(len)) by solve() using {
    to_integer(old(len) - at(before_decrement, len)) == to_integer(old(len)) - at(before_decrement, to_integer(len));
    to_integer(1u64) <= at(before_decrement, to_integer(len));
   };
   have to_integer(old(len) - at(before_decrement, len)) <= 14 by solve() using {
    to_integer(old(len) - at(before_decrement, len)) == to_integer(old(len)) - at(before_decrement, to_integer(len));
    to_integer(old(len)) <= 15;
    to_integer(1u64) <= at(before_decrement, to_integer(len));
   };
   have (old(len) - at(before_decrement, len)) <= 14u64;
   have old(len) - at(before_decrement, len) <= 22208u64 by solve() using { old(len) - at(before_decrement, len) <= 14u64; };
   have old(len) - at(before_decrement, len) <= 15u64 by solve() using { old(len) - at(before_decrement, len) <= 14u64; };
   apply(zlib_prefix_pointer(old(buf), old(len), at(before_decrement, len)));
   have __click_call_result0 == old(buf) + zlib_prefix_count(old(len), at(before_decrement, len)) by solve() using {
    __click_call_result0 == old(buf) + (old(len) - at(before_decrement, len));
    old(buf) + (old(len) - at(before_decrement, len)) == old(buf) + zlib_prefix_count(old(len), at(before_decrement, len));
   };
   have __click_call_result0[0] == old(buf)[zlib_prefix_count(old(len), at(before_decrement, len))] by solve() using {
    __click_call_result0 == old(buf) + zlib_prefix_count(old(len), at(before_decrement, len));
   };
   apply(zlib_byte_u64(__click_call_result0[0]));
   apply(zlib_byte_integer_identity(__click_call_result0[0]));
   have to_integer(adler) <= 3571 by solve() using {
    to_integer(adler) <= 1 + 255 * (to_integer(old(len)) - at(before_decrement, to_integer(len)));
    to_integer(old(len)) <= 15;
    to_integer(1u64) <= at(before_decrement, to_integer(len));
   };
   have to_integer(adler) + to_integer(__click_call_result0[0] as uint32 as uint64) <= 18446744073709551615 by solve() using {
    to_integer(adler) <= 3571;
    to_integer(__click_call_result0[0] as uint32 as uint64) == to_integer(__click_call_result0[0] as int32);
    to_integer(__click_call_result0[0] as int32) <= 255;
   };
   have to_integer(adler + __click_call_result0[0] as uint32 as uint64) == to_integer(adler) + to_integer(__click_call_result0[0] as uint32 as uint64);
   mark before_add;
   step();
   have adler == at(before_add, adler + __click_call_result0[0] as uint32 as uint64) by solve();
   have to_integer(adler) == at(before_add, to_integer(adler + __click_call_result0[0] as uint32 as uint64)) by solve() using { adler == at(before_add, adler + __click_call_result0[0] as uint32 as uint64); };
   have to_integer(adler) == at(before_add, to_integer(adler)) + at(before_add, to_integer(__click_call_result0[0] as int32)) by solve() using {
    to_integer(adler) == at(before_add, to_integer(adler + __click_call_result0[0] as uint32 as uint64));
    at(before_add, to_integer(adler + __click_call_result0[0] as uint32 as uint64)) == at(before_add, to_integer(adler)) + at(before_add, to_integer(__click_call_result0[0] as uint32 as uint64));
    at(before_add, to_integer(__click_call_result0[0] as uint32 as uint64)) == at(before_add, to_integer(__click_call_result0[0] as int32));
   };
   have 1 <= to_integer(adler) by solve() using {
    1 <= at(before_add, to_integer(adler));
    0 <= at(before_add, to_integer(__click_call_result0[0] as int32));
    to_integer(adler) == at(before_add, to_integer(adler)) + at(before_add, to_integer(__click_call_result0[0] as int32));
   };
   have to_integer(adler) <= 1 + 255 * (to_integer(old(len)) - to_integer(len)) by solve() using {
    at(before_add, to_integer(adler)) <= 1 + 255 * (to_integer(old(len)) - at(before_decrement, to_integer(len)));
    at(before_add, to_integer(__click_call_result0[0] as int32)) <= 255;
    to_integer(adler) == at(before_add, to_integer(adler)) + at(before_add, to_integer(__click_call_result0[0] as int32));
    to_integer(len) == at(before_decrement, to_integer(len)) - 1;
   };
   have to_integer(adler) <= 3826 by solve() using {
    at(before_add, to_integer(adler)) <= 3571;
    at(before_add, to_integer(__click_call_result0[0] as int32)) <= 255;
    to_integer(adler) == at(before_add, to_integer(adler)) + at(before_add, to_integer(__click_call_result0[0] as int32));
   };
   have to_integer(sum2) + to_integer(adler) <= 18446744073709551615 by solve() using {
    to_integer(sum2) <= 57390;
    to_integer(adler) <= 3826;
   };
   have to_integer(sum2 + adler) == to_integer(sum2) + to_integer(adler);
   mark before_sum;
   step_until(back_edge());
   have to_integer(sum2) == at(before_sum, to_integer(sum2)) + to_integer(adler) by solve();
   have 0 <= to_integer(sum2);
   have to_integer(sum2) <= 3826 * (to_integer(old(len)) - to_integer(len)) by solve() using {
    at(before_sum, to_integer(sum2)) <= 3826 * (to_integer(old(len)) - at(before_decrement, to_integer(len)));
    to_integer(adler) <= 3826;
    to_integer(sum2) == at(before_sum, to_integer(sum2)) + to_integer(adler);
    to_integer(len) == at(before_decrement, to_integer(len)) - 1;
   };
   have to_integer(sum2) <= 57390 by solve() using {
    to_integer(sum2) <= 3826 * (to_integer(old(len)) - to_integer(len));
    to_integer(old(len)) <= 15;
    0 <= to_integer(len);
   };
   have to_integer(len) <= to_integer(old(len)) by solve() using {
    to_integer(len) == at(before_decrement, to_integer(len)) - 1;
    at(before_decrement, to_integer(len)) <= to_integer(old(len));
   };
   have to_integer(old(len) - len) == to_integer(old(len)) - to_integer(len);
   have to_integer(old(len) - at(before_decrement, len)) <= 14 by solve() using {
    to_integer(old(len) - at(before_decrement, len)) == to_integer(old(len)) - at(before_decrement, to_integer(len));
    to_integer(old(len)) <= 15;
    to_integer(1u64) <= at(before_decrement, to_integer(len));
   };
   have to_integer(old(len) - at(before_decrement, len)) + to_integer(1u64) <= 18446744073709551615 by solve() using { to_integer(old(len) - at(before_decrement, len)) <= 14; };
   have to_integer((old(len) - at(before_decrement, len)) + 1u64) == to_integer(old(len) - at(before_decrement, len)) + to_integer(1u64);
   have to_integer(old(len) - len) == to_integer((old(len) - at(before_decrement, len)) + 1u64) by solve() using {
    to_integer(old(len) - len) == to_integer(old(len)) - to_integer(len);
    to_integer(len) == at(before_decrement, to_integer(len)) - 1;
    to_integer(old(len) - at(before_decrement, len)) == to_integer(old(len)) - at(before_decrement, to_integer(len));
    to_integer((old(len) - at(before_decrement, len)) + 1u64) == to_integer(old(len) - at(before_decrement, len)) + to_integer(1u64);
   };
   have buf == at(before_decrement, buf) + 1 by solve();
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
   have to_integer(len) == to_integer(at(before_decrement, len) - 1u64) by solve();
   have len == (at(before_decrement, len) - 1u64);
   have len <= at(before_decrement, len) - 1u64 by solve();
   have len <= 15u64;
   have len <= 9223372036854775807u64;
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
    have to_integer(old(len) - len) <= 15 by solve() using {
     to_integer(old(len) - len) == to_integer(old(len)) - to_integer(len);
     to_integer(old(len)) <= 15;
     0 <= to_integer(len);
    };
    have (old(len) - len) <= 15u64;
   }
   have old(len) - len <= 22208u64 by solve() using { old(len) - len <= 15u64; };
   apply(zlib_prefix_observation(old(len), len));
   apply(zlib_prefix_observation(old(len), at(before_decrement, len)));
   have to_integer(zlib_prefix_count(old(len), len)) == to_integer(zlib_prefix_count(old(len), at(before_decrement, len))) + 1 by solve() using {
    to_integer(zlib_prefix_count(old(len), len)) == to_integer(old(len) - len);
    to_integer(zlib_prefix_count(old(len), at(before_decrement, len))) == to_integer(old(len) - at(before_decrement, len));
    to_integer(old(len) - len) == to_integer(old(len)) - to_integer(len);
    to_integer(old(len) - at(before_decrement, len)) == to_integer(old(len)) - at(before_decrement, to_integer(len));
    to_integer(len) == at(before_decrement, to_integer(len)) - 1;
   };

   have 0 < to_integer(zlib_prefix_count(old(len), len)) by solve() using {
    to_integer(zlib_prefix_count(old(len), len)) == to_integer(zlib_prefix_count(old(len), at(before_decrement, len))) + 1;
    to_integer(zlib_prefix_count(old(len), at(before_decrement, len))) == to_integer(old(len) - at(before_decrement, len));
    to_integer(old(len) - at(before_decrement, len)) == to_integer(old(len)) - at(before_decrement, to_integer(len));
    at(before_decrement, to_integer(len)) <= to_integer(old(len));
   };
   have to_integer(1) <= to_integer(zlib_prefix_count(old(len), len)) by solve() using { 0 < to_integer(zlib_prefix_count(old(len), len)); };
   have 1 <= zlib_prefix_count(old(len), len);
   apply(zlib_positive_count(zlib_prefix_count(old(len), len)));
   have defined(zlib_prefix_count(old(len), len) - 1);
   have to_integer(zlib_prefix_count(old(len), len) - 1) == to_integer(zlib_prefix_count(old(len), len)) - to_integer(1);
   have to_integer(zlib_prefix_count(old(len), len) - 1) == to_integer(zlib_prefix_count(old(len), at(before_decrement, len))) by solve() using {
    to_integer(zlib_prefix_count(old(len), len) - 1) == to_integer(zlib_prefix_count(old(len), len)) - to_integer(1);
    to_integer(zlib_prefix_count(old(len), len)) == to_integer(zlib_prefix_count(old(len), at(before_decrement, len))) + 1;
   };
   apply(zlib_prefix_append(old(buf), old(len), len));
   apply(adler_weighted_prefix_step(old(buf), zlib_prefix_count(old(len), len)));
   have old(buf)[zlib_prefix_count(old(len), len) - 1] == at(before_add, __click_call_result0[0]) by solve() using {
    zlib_prefix_count(old(len), len) - 1 == zlib_prefix_count(old(len), at(before_decrement, len));
    at(before_add, __click_call_result0[0]) == old(buf)[zlib_prefix_count(old(len), at(before_decrement, len))];
   };
   have adler_byte_sum(old(buf), zlib_prefix_count(old(len), len) - 1) == adler_byte_sum(old(buf), zlib_prefix_count(old(len), at(before_decrement, len))) by solve() using {
    zlib_prefix_count(old(len), len) - 1 == zlib_prefix_count(old(len), at(before_decrement, len));
   };
   have adler_weighted_sum(old(buf), zlib_prefix_count(old(len), len) - 1, zlib_prefix_count(old(len), len) - 1) == adler_weighted_sum(old(buf), zlib_prefix_count(old(len), at(before_decrement, len)), zlib_prefix_count(old(len), at(before_decrement, len))) by solve() using {
    zlib_prefix_count(old(len), len) - 1 == zlib_prefix_count(old(len), at(before_decrement, len));
   };
   apply(zlib_equal_byte_integers(old(buf)[zlib_prefix_count(old(len), len) - 1], at(before_add, __click_call_result0[0])));
   have zlib_byte_integer(old(buf)[zlib_prefix_count(old(len), len) - 1]) == at(before_add, to_integer(__click_call_result0[0] as int32)) by solve() using {
    zlib_byte_integer(old(buf)[zlib_prefix_count(old(len), len) - 1]) == zlib_byte_integer(at(before_add, __click_call_result0[0]));
    at(before_add, zlib_byte_integer(__click_call_result0[0])) == at(before_add, to_integer(__click_call_result0[0] as int32));
   };
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), zlib_prefix_count(old(len), len)) by solve() using {
    adler_byte_sum(old(buf), zlib_prefix_count(old(len), len)) == adler_byte_sum(old(buf), zlib_prefix_count(old(len), len) - 1) + zlib_byte_integer(old(buf)[zlib_prefix_count(old(len), len) - 1]);
    adler_byte_sum(old(buf), zlib_prefix_count(old(len), len) - 1) == adler_byte_sum(old(buf), zlib_prefix_count(old(len), at(before_decrement, len)));
    zlib_byte_integer(old(buf)[zlib_prefix_count(old(len), len) - 1]) == at(before_add, to_integer(__click_call_result0[0] as int32));
    to_integer(adler) == at(before_add, to_integer(adler)) + at(before_add, to_integer(__click_call_result0[0] as int32));
    at(before_add, to_integer(adler)) == 1 + adler_byte_sum(old(buf), zlib_prefix_count(old(len), at(before_decrement, len)));
   };
   have to_integer(sum2) == to_integer(zlib_prefix_count(old(len), len)) + adler_weighted_sum(old(buf), zlib_prefix_count(old(len), len), zlib_prefix_count(old(len), len)) by solve() using {
    adler_weighted_sum(old(buf), zlib_prefix_count(old(len), len), zlib_prefix_count(old(len), len)) == adler_weighted_sum(old(buf), zlib_prefix_count(old(len), len) - 1, zlib_prefix_count(old(len), len) - 1) + adler_byte_sum(old(buf), zlib_prefix_count(old(len), len));
    adler_weighted_sum(old(buf), zlib_prefix_count(old(len), len) - 1, zlib_prefix_count(old(len), len) - 1) == adler_weighted_sum(old(buf), zlib_prefix_count(old(len), at(before_decrement, len)), zlib_prefix_count(old(len), at(before_decrement, len)));
    to_integer(sum2) == at(before_sum, to_integer(sum2)) + to_integer(adler);
    at(before_sum, to_integer(sum2)) == to_integer(zlib_prefix_count(old(len), at(before_decrement, len))) + adler_weighted_sum(old(buf), zlib_prefix_count(old(len), at(before_decrement, len)), zlib_prefix_count(old(len), at(before_decrement, len)));
    to_integer(adler) == 1 + adler_byte_sum(old(buf), zlib_prefix_count(old(len), len));
    to_integer(zlib_prefix_count(old(len), len)) == to_integer(zlib_prefix_count(old(len), at(before_decrement, len))) + 1;
   };
   close_invariants() by { solve(); }
   }
  }
 }
 have adler <= 3826u64;
 have sum2 <= 57390u64;
 have adler < 65521u64 by solve() using { adler <= 3826u64; };
 apply(integer::uint64_less_than_implies_not_greater_equal(adler, 65521u64));
 step_until(assignment(sum2, 4));
 apply(zlib_short_result(old(buf), old(len as uint32 as int32), adler, sum2));
 apply(integer::uint64_remainder_to_integer(sum2, 65521u64));
 apply(integer::positive_divisor_remainder_upper(to_integer(sum2), 65521));
 mark before_reduction;
 step();
 have sum2 == at(before_reduction, sum2 % 65521u64) by solve();
 have to_integer(sum2) == at(before_reduction, to_integer(sum2 % 65521u64)) by solve() using { sum2 == at(before_reduction, sum2 % 65521u64); };
 have to_integer(sum2) <= 65520 by solve() using {
  to_integer(sum2) == at(before_reduction, to_integer(sum2 % 65521u64));
  at(before_reduction, to_integer(sum2 % 65521u64)) == truncating_remainder(at(before_reduction, to_integer(sum2)), 65521);
  truncating_remainder(at(before_reduction, to_integer(sum2)), 65521) <= 65521 - 1;
 };
 have sum2 <= 65520u64;
 have adler <= 65535u64 by solve() using { adler <= 3826u64; };
 have sum2 <= 65535u64 by solve() using { sum2 <= 65520u64; };
 apply(integer::uint64_pack_uint16_to_integer(adler, sum2));
 have to_integer(adler | (sum2 << 16)) <= to_integer(4294967295u64) by solve() using {
  to_integer(adler | (sum2 << 16)) == to_integer(adler) + 65536 * to_integer(sum2);
  to_integer(adler) <= 3826;
  to_integer(sum2) <= 65520;
 };
 have (adler | (sum2 << 16)) <= 4294967295u64;
 apply(adler_spec_checksum_bridge(old(buf), old(len as uint32 as int32), old(len), 1, 0)) using { to_integer(old(len as uint32 as int32)) == to_integer(old(len)); };
}
