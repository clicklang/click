import click::integer;
import click::rust::slice;

verifying "../../vendor/adler2-2.0.1/src/lib.rs";

theorem adler_helper_byte_observation(value: uint8) {
 ensures to_integer((value as u32)) == to_integer((value as i32)) by {
  have 0 <= (value as i32);
  have (value as i32) <= 255;
  close() using { 0 <= to_integer((value as i32)); to_integer((value as i32)) <= 255; };
 }
}

impl adler2::algo::U32X4 {
    fn from(bytes: &[u8]) -> adler2::algo::U32X4 {
        requires bytes.len() >= 4u64;
        views bytes[0..4];
        ensures result.0[0] == bytes[0];
        ensures result.0[1] == bytes[1];
        ensures result.0[2] == bytes[2];
        ensures result.0[3] == bytes[3];
        ensures result.0[0] <= 255u32;
        ensures result.0[1] <= 255u32;
        ensures result.0[2] <= 255u32;
        ensures result.0[3] <= 255u32;
        ensures 0 <= to_integer(result.0[0]);
        ensures to_integer(result.0[0]) <= 255;
        ensures 0 <= to_integer(result.0[1]);
        ensures to_integer(result.0[1]) <= 255;
        ensures 0 <= to_integer(result.0[2]);
        ensures to_integer(result.0[2]) <= 255;
        ensures 0 <= to_integer(result.0[3]);
        ensures to_integer(result.0[3]) <= 255;
        ensures to_integer(result.0[0]) == old(to_integer((bytes[0] as i32)));
        ensures to_integer(result.0[1]) == old(to_integer((bytes[1] as i32)));
        ensures to_integer(result.0[2]) == old(to_integer((bytes[2] as i32)));
        ensures to_integer(result.0[3]) == old(to_integer((bytes[3] as i32)));
    } by {
        apply(adler_helper_byte_observation(bytes[0]));
        apply(adler_helper_byte_observation(bytes[1]));
        apply(adler_helper_byte_observation(bytes[2]));
        apply(adler_helper_byte_observation(bytes[3]));
        // The aggregate stores use fresh storage. Read the bound result at return.
        step_until(function.exit);
        have result.0[0] == old((bytes[0] as u32));
        have to_integer(result.0[0]) == old(to_integer((bytes[0] as i32))) by { rewrite(result.0[0], old((bytes[0] as u32))); known(); }
        have result.0[1] == old((bytes[1] as u32));
        have to_integer(result.0[1]) == old(to_integer((bytes[1] as i32))) by { rewrite(result.0[1], old((bytes[1] as u32))); known(); }
        have result.0[2] == old((bytes[2] as u32));
        have to_integer(result.0[2]) == old(to_integer((bytes[2] as i32))) by { rewrite(result.0[2], old((bytes[2] as u32))); known(); }
        have result.0[3] == old((bytes[3] as u32));
        have to_integer(result.0[3]) == old(to_integer((bytes[3] as i32))) by { rewrite(result.0[3], old((bytes[3] as u32))); known(); }
        // Establish the byte ranges independently of the ensures clauses, then
        // close from those checked witnesses so false bounds fail without search.
        have 255u32 >= result.0[0];
        have to_integer(result.0[0]) >= 0;
        have 255 >= to_integer(result.0[0]);
        have 255u32 >= result.0[1];
        have to_integer(result.0[1]) >= 0;
        have 255 >= to_integer(result.0[1]);
        have 255u32 >= result.0[2];
        have to_integer(result.0[2]) >= 0;
        have 255 >= to_integer(result.0[2]);
        have 255u32 >= result.0[3];
        have to_integer(result.0[3]) >= 0;
        have 255 >= to_integer(result.0[3]);
        close() using {
            result.0[0] == old((bytes[0] as u32));
            to_integer(result.0[0]) == old(to_integer((bytes[0] as i32)));
            255u32 >= result.0[0];
            to_integer(result.0[0]) >= 0;
            255 >= to_integer(result.0[0]);
            result.0[1] == old((bytes[1] as u32));
            to_integer(result.0[1]) == old(to_integer((bytes[1] as i32)));
            255u32 >= result.0[1];
            to_integer(result.0[1]) >= 0;
            255 >= to_integer(result.0[1]);
            result.0[2] == old((bytes[2] as u32));
            to_integer(result.0[2]) == old(to_integer((bytes[2] as i32)));
            255u32 >= result.0[2];
            to_integer(result.0[2]) >= 0;
            255 >= to_integer(result.0[2]);
            result.0[3] == old((bytes[3] as u32));
            to_integer(result.0[3]) == old(to_integer((bytes[3] as i32)));
            255u32 >= result.0[3];
            to_integer(result.0[3]) >= 0;
            255 >= to_integer(result.0[3]);
        };
    }
}

impl AddAssign<adler2::algo::U32X4> for adler2::algo::U32X4 {
    fn add_assign(&mut self, other: adler2::algo::U32X4) {
        requires to_integer(self.0[0]) + to_integer(other.0[0]) <= 4294967295;
        requires to_integer(self.0[1]) + to_integer(other.0[1]) <= 4294967295;
        requires to_integer(self.0[2]) + to_integer(other.0[2]) <= 4294967295;
        requires to_integer(self.0[3]) + to_integer(other.0[3]) <= 4294967295;
        owns self.0[0..4];
        ensures to_integer(self.0[0]) == to_integer(old(self.0[0]) + other.0[0]);
        ensures to_integer(self.0[1]) == to_integer(old(self.0[1]) + other.0[1]);
        ensures to_integer(self.0[2]) == to_integer(old(self.0[2]) + other.0[2]);
        ensures to_integer(self.0[3]) == to_integer(old(self.0[3]) + other.0[3]);
        ensures to_integer(self.0[0]) == to_integer(old(self.0[0])) + to_integer(other.0[0]);
        ensures 0 <= to_integer(self.0[0]);
        ensures to_integer(self.0[1]) == to_integer(old(self.0[1])) + to_integer(other.0[1]);
        ensures 0 <= to_integer(self.0[1]);
        ensures to_integer(self.0[2]) == to_integer(old(self.0[2])) + to_integer(other.0[2]);
        ensures 0 <= to_integer(self.0[2]);
        ensures to_integer(self.0[3]) == to_integer(old(self.0[3])) + to_integer(other.0[3]);
        ensures 0 <= to_integer(self.0[3]);
    } by {
        have self.0[0] <= 4294967295u32 - other.0[0] by { close() using { to_integer(self.0[0]) + to_integer(other.0[0]) <= 4294967295; }; }
        have self.0[1] <= 4294967295u32 - other.0[1] by { close() using { to_integer(self.0[1]) + to_integer(other.0[1]) <= 4294967295; }; }
        have self.0[2] <= 4294967295u32 - other.0[2] by { close() using { to_integer(self.0[2]) + to_integer(other.0[2]) <= 4294967295; }; }
        have self.0[3] <= 4294967295u32 - other.0[3] by { close() using { to_integer(self.0[3]) + to_integer(other.0[3]) <= 4294967295; }; }
    }
}

impl RemAssign<u32> for adler2::algo::U32X4 {
    fn rem_assign(&mut self, quotient: u32) {
        requires quotient != 0u32;
        owns self.0[0..4];
        ensures self.0[0] == old(self.0[0]) % quotient;
        ensures self.0[1] == old(self.0[1]) % quotient;
        ensures self.0[2] == old(self.0[2]) % quotient;
        ensures self.0[3] == old(self.0[3]) % quotient;
        ensures to_integer(self.0[0]) == truncating_remainder(to_integer(old(self.0[0])), to_integer(quotient));
        ensures to_integer(self.0[1]) == truncating_remainder(to_integer(old(self.0[1])), to_integer(quotient));
        ensures to_integer(self.0[2]) == truncating_remainder(to_integer(old(self.0[2])), to_integer(quotient));
        ensures to_integer(self.0[3]) == truncating_remainder(to_integer(old(self.0[3])), to_integer(quotient));
        ensures self.0[0] < quotient;
        ensures 0 <= to_integer(self.0[0]);
        ensures to_integer(self.0[0]) < to_integer(quotient);
        ensures self.0[1] < quotient;
        ensures 0 <= to_integer(self.0[1]);
        ensures to_integer(self.0[1]) < to_integer(quotient);
        ensures self.0[2] < quotient;
        ensures 0 <= to_integer(self.0[2]);
        ensures to_integer(self.0[2]) < to_integer(quotient);
        ensures self.0[3] < quotient;
        ensures 0 <= to_integer(self.0[3]);
        ensures to_integer(self.0[3]) < to_integer(quotient);
        ensures old(self.0[0]) < quotient implies self.0[0] == old(self.0[0]);
        ensures old(self.0[1]) < quotient implies self.0[1] == old(self.0[1]);
        ensures old(self.0[2]) < quotient implies self.0[2] == old(self.0[2]);
        ensures old(self.0[3]) < quotient implies self.0[3] == old(self.0[3]);
    } by {
        apply(integer::uint32_remainder_to_integer(self.0[0], quotient));
        apply(integer::uint32_remainder_to_integer(self.0[1], quotient));
        apply(integer::uint32_remainder_to_integer(self.0[2], quotient));
        apply(integer::uint32_remainder_to_integer(self.0[3], quotient));
        step_until(function.exit);
        have self.0[0] == old(self.0[0]) % quotient;
        have to_integer(self.0[0]) == truncating_remainder(to_integer(old(self.0[0])), to_integer(quotient)) by {
            rewrite(self.0[0], old(self.0[0]) % quotient);
            known();
        }
        have self.0[1] == old(self.0[1]) % quotient;
        have to_integer(self.0[1]) == truncating_remainder(to_integer(old(self.0[1])), to_integer(quotient)) by {
            rewrite(self.0[1], old(self.0[1]) % quotient);
            known();
        }
        have self.0[2] == old(self.0[2]) % quotient;
        have to_integer(self.0[2]) == truncating_remainder(to_integer(old(self.0[2])), to_integer(quotient)) by {
            rewrite(self.0[2], old(self.0[2]) % quotient);
            known();
        }
        have self.0[3] == old(self.0[3]) % quotient;
        have to_integer(self.0[3]) == truncating_remainder(to_integer(old(self.0[3])), to_integer(quotient)) by {
            rewrite(self.0[3], old(self.0[3]) % quotient);
            known();
        }
        apply(integer::uint32_remainder_less_than_divisor(old(self.0[0]), quotient));
        have self.0[0] < quotient;
        apply(integer::uint32_remainder_less_than_divisor(old(self.0[1]), quotient));
        have self.0[1] < quotient;
        apply(integer::uint32_remainder_less_than_divisor(old(self.0[2]), quotient));
        have self.0[2] < quotient;
        apply(integer::uint32_remainder_less_than_divisor(old(self.0[3]), quotient));
        have self.0[3] < quotient;
        have old(self.0[0]) < quotient implies self.0[0] == old(self.0[0]) by {
            if old(self.0[0]) < quotient {
                apply(integer::uint32_less_than_divisor_implies_remainder_is_value(old(self.0[0]), quotient));
                solve();
            } else { solve(); }
        }
        have old(self.0[1]) < quotient implies self.0[1] == old(self.0[1]) by {
            if old(self.0[1]) < quotient {
                apply(integer::uint32_less_than_divisor_implies_remainder_is_value(old(self.0[1]), quotient));
                solve();
            } else { solve(); }
        }
        have old(self.0[2]) < quotient implies self.0[2] == old(self.0[2]) by {
            if old(self.0[2]) < quotient {
                apply(integer::uint32_less_than_divisor_implies_remainder_is_value(old(self.0[2]), quotient));
                solve();
            } else { solve(); }
        }
        have old(self.0[3]) < quotient implies self.0[3] == old(self.0[3]) by {
            if old(self.0[3]) < quotient {
                apply(integer::uint32_less_than_divisor_implies_remainder_is_value(old(self.0[3]), quotient));
                solve();
            } else { solve(); }
        }
        solve();
    }
}

impl MulAssign<u32> for adler2::algo::U32X4 {
    fn mul_assign(&mut self, rhs: u32) {
        requires rhs == 0u32 or self.0[0] <= 4294967295u32 / rhs;
        requires rhs == 0u32 or self.0[1] <= 4294967295u32 / rhs;
        requires rhs == 0u32 or self.0[2] <= 4294967295u32 / rhs;
        requires rhs == 0u32 or self.0[3] <= 4294967295u32 / rhs;
        owns self.0[0..4];
        ensures to_integer(self.0[0]) == to_integer(old(self.0[0]) * rhs);
        ensures to_integer(self.0[1]) == to_integer(old(self.0[1]) * rhs);
        ensures to_integer(self.0[2]) == to_integer(old(self.0[2]) * rhs);
        ensures to_integer(self.0[3]) == to_integer(old(self.0[3]) * rhs);
        ensures to_integer(self.0[0]) == to_integer(old(self.0[0])) * to_integer(rhs);
        ensures 0 <= to_integer(self.0[0]);
        ensures to_integer(self.0[0]) <= 4294967295;
        ensures to_integer(self.0[1]) == to_integer(old(self.0[1])) * to_integer(rhs);
        ensures 0 <= to_integer(self.0[1]);
        ensures to_integer(self.0[1]) <= 4294967295;
        ensures to_integer(self.0[2]) == to_integer(old(self.0[2])) * to_integer(rhs);
        ensures 0 <= to_integer(self.0[2]);
        ensures to_integer(self.0[2]) <= 4294967295;
        ensures to_integer(self.0[3]) == to_integer(old(self.0[3])) * to_integer(rhs);
        ensures 0 <= to_integer(self.0[3]);
        ensures to_integer(self.0[3]) <= 4294967295;
    } by {
        step_until(function.exit);
        apply(integer::uint32_multiply_to_integer(old(self.0[0]), rhs));
        apply(integer::uint32_multiply_to_integer(old(self.0[1]), rhs));
        apply(integer::uint32_multiply_to_integer(old(self.0[2]), rhs));
        apply(integer::uint32_multiply_to_integer(old(self.0[3]), rhs));
        solve();
    }
}

// Empty-input boundary of the original, locked Adler32::compute body.
// The preceding helper bodies and both constant getters are checked here too.
impl adler2::Adler32 {
    fn compute(&mut self, bytes: &[u8]) {
     requires bytes.len() == 0u64;
     requires self.a == 1;
     requires self.b == 0;
     owns self.a;
     owns self.b;
     views bytes[0..0];
     ensures self.a == 1;
     ensures self.b == 0;
    } by {
     // The empty chunk iterators execute no body. Prove the scalar reduction
     // from its checked transition before following lane recombination.
     step_until(assignment(b, 0).entry); step();
     have a == 1u32 by { known(); }
     have b == 0u32;
     // Neither chunk iterator has any bytes available to yield.
     step_until(loop(0).entry);
     have loop(0).iter.v.len() == 0u64;
     have remainder_chunk.len() == 0u64;
     step_until(loop(2).entry);
     have loop(2).iter.v.len() == 0u64;
     step_until(assignment(b, 3).entry);
     have b == 0u32;
     have remainder_chunk.len() == 0u64;
     step();
     have b == 0u32;
     step_until(assignment(b, 4).entry);
     mark scalar_mod;
     have at(scalar_mod, b) == 0u32;
     step();
     have b == at(scalar_mod, b) % 65521u32;
     have b == 0u32 by {
     rewrite(b, at(scalar_mod, b) % 65521u32);
     rewrite(at(scalar_mod, b), 0u32);
     solve();
     }
     // Both lane vectors are still zero: neither loop ran, and each reduction
     // and the multiplication by four keep a zero lane zero.
     have a_vec.0[0] == 0u32;
     have a_vec.0[1] == 0u32;
     have a_vec.0[2] == 0u32;
     have a_vec.0[3] == 0u32;
     have b_vec.0[0] == 0u32;
     have b_vec.0[1] == 0u32;
     have b_vec.0[2] == 0u32;
     have b_vec.0[3] == 0u32;
     have b_vec.0[0] <= 1073741823u32 by close() using { b_vec.0[0] == 0u32; };
     have b_vec.0[1] <= 1073741823u32 by close() using { b_vec.0[1] == 0u32; };
     have b_vec.0[2] <= 1073741823u32 by close() using { b_vec.0[2] == 0u32; };
     have b_vec.0[3] <= 1073741823u32 by close() using { b_vec.0[3] == 0u32; };
     // The three corrections add MOD, twice MOD, and three times MOD.
     step_until(statement(16).entry);
     have b_vec.0[0] == 0u32;
     have b_vec.0[1] == 0u32;
     have b_vec.0[2] == 0u32;
     have b_vec.0[3] == 0u32;
     step_until(statement(17).entry);
     have b_vec.0[1] == 65521u32;
     step_until(statement(18).entry);
     have b_vec.0[2] == 131042u32;
     step_until(loop(3).entry);
     have a == 1u32;
     have b == 0u32;
     have a_vec.0[0] == 0u32;
     have a_vec.0[1] == 0u32;
     have a_vec.0[2] == 0u32;
     have a_vec.0[3] == 0u32;
     have b_vec.0[0] == 0u32;
     have b_vec.0[1] == 65521u32;
     have b_vec.0[2] == 131042u32;
     have b_vec.0[3] == 196563u32;
     // Read-only array iteration sums all four original lanes in order.
     mark before_sum_a;
     have at(before_sum_a, a) == 1u32;
     have at(before_sum_a, a_vec.0[0]) == 0u32;
     have at(before_sum_a, a_vec.0[1]) == 0u32;
     have at(before_sum_a, a_vec.0[2]) == 0u32;
     have at(before_sum_a, a_vec.0[3]) == 0u32;
     step_until(loop(4).entry);
     have a == at(before_sum_a, a) + at(before_sum_a, a_vec.0[0]) + at(before_sum_a, a_vec.0[1]) + at(before_sum_a, a_vec.0[2]) + at(before_sum_a, a_vec.0[3]);
     have a == 1u32 by {
     rewrite(a, at(before_sum_a, a) + at(before_sum_a, a_vec.0[0]) + at(before_sum_a, a_vec.0[1]) + at(before_sum_a, a_vec.0[2]) + at(before_sum_a, a_vec.0[3]));
     rewrite(at(before_sum_a, a), 1u32);
     rewrite(at(before_sum_a, a_vec.0[0]), 0u32);
     rewrite(at(before_sum_a, a_vec.0[1]), 0u32);
     rewrite(at(before_sum_a, a_vec.0[2]), 0u32);
     rewrite(at(before_sum_a, a_vec.0[3]), 0u32);
     solve();
     }
     mark before_sum_b;
     have at(before_sum_b, b) == 0u32;
     have at(before_sum_b, b_vec.0[0]) == 0u32;
     have at(before_sum_b, b_vec.0[1]) == 65521u32;
     have at(before_sum_b, b_vec.0[2]) == 131042u32;
     have at(before_sum_b, b_vec.0[3]) == 196563u32;
     step_until(loop(5).entry);
     have b == at(before_sum_b, b) + at(before_sum_b, b_vec.0[0]) + at(before_sum_b, b_vec.0[1]) + at(before_sum_b, b_vec.0[2]) + at(before_sum_b, b_vec.0[3]) by {
     rewrite(at(before_sum_b, b), 0u32);
     rewrite(at(before_sum_b, b_vec.0[0]), 0u32);
     rewrite(at(before_sum_b, b_vec.0[1]), 65521u32);
     rewrite(at(before_sum_b, b_vec.0[2]), 131042u32);
     rewrite(at(before_sum_b, b_vec.0[3]), 196563u32);
     solve();
     }
     have b == 393126u32 by {
     rewrite(b, at(before_sum_b, b) + at(before_sum_b, b_vec.0[0]) + at(before_sum_b, b_vec.0[1]) + at(before_sum_b, b_vec.0[2]) + at(before_sum_b, b_vec.0[3]));
     rewrite(at(before_sum_b, b), 0u32);
     rewrite(at(before_sum_b, b_vec.0[0]), 0u32);
     rewrite(at(before_sum_b, b_vec.0[1]), 65521u32);
     rewrite(at(before_sum_b, b_vec.0[2]), 131042u32);
     rewrite(at(before_sum_b, b_vec.0[3]), 196563u32);
     solve();
     }
     // The serial tail is empty. Reduce the two sums before narrowing.
     step_until(statement(22).entry);
     mark output_a;
     have at(output_a, a) == 1u32;
     step_until(statement(23).entry);
     have self.a == 1;
     mark output_b;
     have at(output_b, b) == 393126u32;
     step_until(function.exit);
     have self.b == 0;
     known();
     known();
     known();
     known();
    }
}

// Imported scalar constants
impl adler2::Adler32 {
    fn compute::MOD() -> u32 { ensures result == 65521u32; }
}
impl adler2::Adler32 {
    fn compute::CHUNK_SIZE() -> usize { ensures result == 22208u64; }
}
