target "x86_64-linux-userspace";
verifying "adler32.c";
uint64 adler32_z(uint64 adler, const uint8* buf, uint64 len) {
 requires adler == 1u64;
 requires 2u64 <= len;
 requires len <= 15u64;
 requires buf != 0;
 views buf[0u64..len];
 ensures forall (k: uint64) { k < old(len) implies old(buf)[k] == old(buf[k]) };
} by {
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
  initialize by { apply(uint64_less_equal_to_integer(len, 15u64)); simp(); }
  preserve by {
   if len == 0u64 {
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
   execute_until(back_edge());
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
   close_invariants by { simp(); }
   }
  }
 }
 execute(); simp();
}
