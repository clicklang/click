// Four-byte boundary of the original, locked Adler32::compute body.
// The fixture harness combines this contract with the helper/getter contracts
// from helpers.click, checks all their bodies, and rechecks the proof tools.
impl adler2::Adler32 {
    fn compute(&mut self, bytes: &[u8]) {
     requires bytes.len() == 4u64;
     requires self.a == 1;
     requires self.b == 0;
     owns self.a;
     owns self.b;
     views bytes[0..4];
     ensures to_integer(self.a) == to_integer((((((1u32 + (old((bytes[0] as u32)))) + (old((bytes[1] as u32)))) + (old((bytes[2] as u32)))) + (old((bytes[3] as u32))))) % 65521u32);
     ensures to_integer(self.b) == to_integer((((((4u32 + (old((bytes[0] as u32)) * 4u32)) + (old((bytes[1] as u32)) * 4u32 + (65521u32 - old((bytes[1] as u32))))) + (old((bytes[2] as u32)) * 4u32 + ((65521u32 - old((bytes[2] as u32))) * 2u32))) + (old((bytes[3] as u32)) * 4u32 + ((65521u32 - old((bytes[3] as u32))) * 3u32)))) % 65521u32);
     ensures bytes[0] == old(bytes[0]);
     ensures bytes[1] == old(bytes[1]);
     ensures bytes[2] == old(bytes[2]);
     ensures bytes[3] == old(bytes[3]);
     ensures to_integer(self.a) == old(adler_spec_a(bytes, 4, 1));
     ensures to_integer(self.b) == old(adler_spec_b(bytes, 4, 1, 0));
    } by {
     apply(adler_four_byte_result_spec(bytes));
     have old(bytes.len()) == 4u64 by { known(); }
     step_until(assignment(b, 0)); step();
     have a == 1u32 by { known(); }
     step_until(loop(0));
     // Four bytes fit in the remainder and form exactly one lane vector.
     have remainder_chunk.len() == 4u64;
     have remainder_chunk == old(bytes);
     have loop(0).iter.chunk_size == 22208u64;
     have loop(0).iter.v.len() == 0u64;
     step_until(loop(2));
     have loop(2).iter.chunk_size == 4u64;
     have loop(2).iter.v.len() == 4u64;
     have loop(2).iter.v == old(bytes);
     step_until(loop(2).statement(0));
     have loop(2).iter.v.len() == 0u64 by { known(); }
     have loop(2).iter.v == old(bytes) + 4u64 by { known(); }
     step_until(loop(2).statement(1));
     have __rust_mir_68.0[0] == old((bytes[0] as u32));
     have to_integer(__rust_mir_68.0[0]) <= 255;
     have to_integer(a_vec.0[0]) == 0;
     have __rust_mir_68.0[1] == old((bytes[1] as u32));
     have to_integer(__rust_mir_68.0[1]) <= 255;
     have to_integer(a_vec.0[1]) == 0;
     have __rust_mir_68.0[2] == old((bytes[2] as u32));
     have to_integer(__rust_mir_68.0[2]) <= 255;
     have to_integer(a_vec.0[2]) == 0;
     have __rust_mir_68.0[3] == old((bytes[3] as u32));
     have to_integer(__rust_mir_68.0[3]) <= 255;
     have to_integer(a_vec.0[3]) == 0;
     step_until(loop(2).statement(2));
     have a_vec.0[0] == old((bytes[0] as u32));
     have to_integer(a_vec.0[0]) <= 255 by { known(); }
     have to_integer(b_vec.0[0]) == 0;
     have a_vec.0[1] == old((bytes[1] as u32));
     have to_integer(a_vec.0[1]) <= 255 by { known(); }
     have to_integer(b_vec.0[1]) == 0;
     have a_vec.0[2] == old((bytes[2] as u32));
     have to_integer(a_vec.0[2]) <= 255 by { known(); }
     have to_integer(b_vec.0[2]) == 0;
     have a_vec.0[3] == old((bytes[3] as u32));
     have to_integer(a_vec.0[3]) <= 255 by { known(); }
     have to_integer(b_vec.0[3]) == 0;
     have to_integer(b_vec.0[3]) + to_integer(a_vec.0[3]) <= 4294967295 by {
      solve() using { to_integer(b_vec.0[3]) == 0; to_integer(a_vec.0[3]) <= 255; };
     }
     step_until(assignment(b, 3));
     have a_vec.0[0] == old((bytes[0] as u32));
     have b_vec.0[0] == old((bytes[0] as u32));
     have to_integer(b_vec.0[0]) <= 255 by { known(); }
     have a_vec.0[1] == old((bytes[1] as u32));
     have b_vec.0[1] == old((bytes[1] as u32));
     have to_integer(b_vec.0[1]) <= 255 by { known(); }
     have a_vec.0[2] == old((bytes[2] as u32));
     have b_vec.0[2] == old((bytes[2] as u32));
     have to_integer(b_vec.0[2]) <= 255 by { known(); }
     have a_vec.0[3] == old((bytes[3] as u32));
     have b_vec.0[3] == old((bytes[3] as u32));
     have to_integer(b_vec.0[3]) <= 255 by { known(); }
     have remainder_chunk.len() == 4u64;
     step();
     have b == 4u32;
     step_until(statement(12));
     mark reduce_a;
     have at(reduce_a, a_vec.0[0]) == old((bytes[0] as u32));
     have at(reduce_a, a_vec.0[0]) <= 255u32;
     have at(reduce_a, a_vec.0[0]) < 65521u32 by solve() using { at(reduce_a, a_vec.0[0]) <= 255u32; };
     have at(reduce_a, a_vec.0[1]) == old((bytes[1] as u32));
     have at(reduce_a, a_vec.0[1]) <= 255u32;
     have at(reduce_a, a_vec.0[1]) < 65521u32 by solve() using { at(reduce_a, a_vec.0[1]) <= 255u32; };
     have at(reduce_a, a_vec.0[2]) == old((bytes[2] as u32));
     have at(reduce_a, a_vec.0[2]) <= 255u32;
     have at(reduce_a, a_vec.0[2]) < 65521u32 by solve() using { at(reduce_a, a_vec.0[2]) <= 255u32; };
     have at(reduce_a, a_vec.0[3]) == old((bytes[3] as u32));
     have at(reduce_a, a_vec.0[3]) <= 255u32;
     have at(reduce_a, a_vec.0[3]) < 65521u32 by solve() using { at(reduce_a, a_vec.0[3]) <= 255u32; };
     step_until(statement(13));
     have statement(12).call(0).result == 65521u32;
     have a_vec.0[0] == at(reduce_a, a_vec.0[0]) % statement(12).call(0).result;
     apply(integer::uint32_less_than_divisor_implies_remainder_is_value(at(reduce_a, a_vec.0[0]), 65521u32));
     have a_vec.0[0] == old((bytes[0] as u32));
     have a_vec.0[1] == at(reduce_a, a_vec.0[1]) % statement(12).call(0).result;
     apply(integer::uint32_less_than_divisor_implies_remainder_is_value(at(reduce_a, a_vec.0[1]), 65521u32));
     have a_vec.0[1] == old((bytes[1] as u32));
     have a_vec.0[2] == at(reduce_a, a_vec.0[2]) % statement(12).call(0).result;
     apply(integer::uint32_less_than_divisor_implies_remainder_is_value(at(reduce_a, a_vec.0[2]), 65521u32));
     have a_vec.0[2] == old((bytes[2] as u32));
     have a_vec.0[3] == at(reduce_a, a_vec.0[3]) % statement(12).call(0).result;
     apply(integer::uint32_less_than_divisor_implies_remainder_is_value(at(reduce_a, a_vec.0[3]), 65521u32));
     have a_vec.0[3] == old((bytes[3] as u32));
     mark reduce_b;
     have at(reduce_b, b_vec.0[0]) == old((bytes[0] as u32));
     have at(reduce_b, b_vec.0[0]) <= 255u32;
     have at(reduce_b, b_vec.0[0]) < 65521u32 by solve() using { at(reduce_b, b_vec.0[0]) <= 255u32; };
     have at(reduce_b, b_vec.0[1]) == old((bytes[1] as u32));
     have at(reduce_b, b_vec.0[1]) <= 255u32;
     have at(reduce_b, b_vec.0[1]) < 65521u32 by solve() using { at(reduce_b, b_vec.0[1]) <= 255u32; };
     have at(reduce_b, b_vec.0[2]) == old((bytes[2] as u32));
     have at(reduce_b, b_vec.0[2]) <= 255u32;
     have at(reduce_b, b_vec.0[2]) < 65521u32 by solve() using { at(reduce_b, b_vec.0[2]) <= 255u32; };
     have at(reduce_b, b_vec.0[3]) == old((bytes[3] as u32));
     have at(reduce_b, b_vec.0[3]) <= 255u32;
     have at(reduce_b, b_vec.0[3]) < 65521u32 by solve() using { at(reduce_b, b_vec.0[3]) <= 255u32; };
     step_until(statement(14));
     have statement(13).call(0).result == 65521u32;
     have b_vec.0[0] == at(reduce_b, b_vec.0[0]) % statement(13).call(0).result by { known(); }
     apply(integer::uint32_less_than_divisor_implies_remainder_is_value(at(reduce_b, b_vec.0[0]), 65521u32));
     have b_vec.0[0] == old((bytes[0] as u32));
     have b_vec.0[1] == at(reduce_b, b_vec.0[1]) % statement(13).call(0).result;
     apply(integer::uint32_less_than_divisor_implies_remainder_is_value(at(reduce_b, b_vec.0[1]), 65521u32));
     have b_vec.0[1] == old((bytes[1] as u32));
     have b_vec.0[2] == at(reduce_b, b_vec.0[2]) % statement(13).call(0).result;
     apply(integer::uint32_less_than_divisor_implies_remainder_is_value(at(reduce_b, b_vec.0[2]), 65521u32));
     have b_vec.0[2] == old((bytes[2] as u32));
     have b_vec.0[3] == at(reduce_b, b_vec.0[3]) % statement(13).call(0).result;
     apply(integer::uint32_less_than_divisor_implies_remainder_is_value(at(reduce_b, b_vec.0[3]), 65521u32));
     have b_vec.0[3] == old((bytes[3] as u32));
     step_until(statement(15));
     have b == 4u32;
     have b_vec.0[0] <= 1073741823u32;
     have b_vec.0[1] <= 1073741823u32;
     have b_vec.0[2] <= 1073741823u32;
     have b_vec.0[3] <= 1073741823u32;
     mark before_weight;
     step_until(statement(16));
     have b_vec.0[0] == at(before_weight, b_vec.0[0]) * 4u32;
     have b_vec.0[0] == old((bytes[0] as u32)) * 4u32;
     have b_vec.0[1] == at(before_weight, b_vec.0[1]) * 4u32;
     have b_vec.0[1] == old((bytes[1] as u32)) * 4u32;
     have b_vec.0[2] == at(before_weight, b_vec.0[2]) * 4u32;
     have b_vec.0[2] == old((bytes[2] as u32)) * 4u32;
     have b_vec.0[3] == at(before_weight, b_vec.0[3]) * 4u32;
     have b_vec.0[3] == old((bytes[3] as u32)) * 4u32;
     have a_vec.0[1] < 65521u32;
     have to_integer(b_vec.0[1]) <= 262080;
     apply(adler_recombine_lane_1(a_vec.0[1], b_vec.0[1]));
     step_until(statement(17));
     have statement(16).call(0).result == 65521u32;
     have b_vec.0[1] == (old((bytes[1] as u32)) * 4u32) + (65521u32 - old((bytes[1] as u32)));
     have a_vec.0[2] < 65521u32;
     have to_integer(b_vec.0[2]) <= 262080;
     apply(adler_recombine_lane_2(a_vec.0[2], b_vec.0[2]));
     step_until(statement(18));
     have statement(17).call(0).result == 65521u32;
     have b_vec.0[2] == (old((bytes[2] as u32)) * 4u32) + ((65521u32 - old((bytes[2] as u32))) * 2u32);
     have a_vec.0[3] < 65521u32;
     have to_integer(b_vec.0[3]) <= 262080;
     apply(adler_recombine_lane_3(a_vec.0[3], b_vec.0[3]));
     step_until(statement(19));
     have statement(18).call(0).result == 65521u32;
     have b_vec.0[3] == (old((bytes[3] as u32)) * 4u32) + ((65521u32 - old((bytes[3] as u32))) * 3u32);
     step_until(loop(3));
     have a == 1u32;
     have to_integer(a) <= 1;
     step_until(loop(3).statement(0));
     have av == a_vec.0[0];
     have av == old((bytes[0] as u32)) by { rewrite(av, a_vec.0[0]); known(); }
     have to_integer(av) <= 255;
     have to_integer(a) + to_integer(av) <= 4294967295 by solve() using { to_integer(a) <= 1; to_integer(av) <= 255; };
     mark sum_a_0;
     apply(integer::uint32_add_to_integer(at(sum_a_0, a), at(sum_a_0, av)));
     step_until(assignment(a, 1)); step();
     have a == at(sum_a_0, a) + at(sum_a_0, av);
     have a == (1u32 + old((bytes[0] as u32)));
     have to_integer(a) == to_integer(at(sum_a_0, a)) + to_integer(at(sum_a_0, av)) by { known(); }
     have to_integer(a) <= 256 by {
      solve() using { to_integer(a) == to_integer(at(sum_a_0, a)) + to_integer(at(sum_a_0, av)); to_integer(at(sum_a_0, a)) <= 1; to_integer(at(sum_a_0, av)) <= 255; };
     }
     step(); step();
     step_until(loop(3).statement(0));
     have av == a_vec.0[1];
     have av == old((bytes[1] as u32)) by { rewrite(av, a_vec.0[1]); known(); }
     have to_integer(av) <= 255;
     have to_integer(a) + to_integer(av) <= 4294967295 by solve() using { to_integer(a) <= 256; to_integer(av) <= 255; };
     mark sum_a_1;
     apply(integer::uint32_add_to_integer(at(sum_a_1, a), at(sum_a_1, av)));
     step_until(assignment(a, 1)); step();
     have a == at(sum_a_1, a) + at(sum_a_1, av);
     have a == ((1u32 + old((bytes[0] as u32))) + old((bytes[1] as u32)));
     have to_integer(a) == to_integer(at(sum_a_1, a)) + to_integer(at(sum_a_1, av)) by { known(); }
     have to_integer(a) <= 511 by {
      solve() using { to_integer(a) == to_integer(at(sum_a_1, a)) + to_integer(at(sum_a_1, av)); to_integer(at(sum_a_1, a)) <= 256; to_integer(at(sum_a_1, av)) <= 255; };
     }
     step(); step();
     step_until(loop(3).statement(0));
     have av == a_vec.0[2];
     have av == old((bytes[2] as u32)) by { rewrite(av, a_vec.0[2]); known(); }
     have to_integer(av) <= 255;
     have to_integer(a) + to_integer(av) <= 4294967295 by solve() using { to_integer(a) <= 511; to_integer(av) <= 255; };
     mark sum_a_2;
     apply(integer::uint32_add_to_integer(at(sum_a_2, a), at(sum_a_2, av)));
     step_until(assignment(a, 1)); step();
     have a == at(sum_a_2, a) + at(sum_a_2, av);
     have a == (((1u32 + old((bytes[0] as u32))) + old((bytes[1] as u32))) + old((bytes[2] as u32)));
     have to_integer(a) == to_integer(at(sum_a_2, a)) + to_integer(at(sum_a_2, av)) by { known(); }
     have to_integer(a) <= 766 by {
      solve() using { to_integer(a) == to_integer(at(sum_a_2, a)) + to_integer(at(sum_a_2, av)); to_integer(at(sum_a_2, a)) <= 511; to_integer(at(sum_a_2, av)) <= 255; };
     }
     step(); step();
     step_until(loop(3).statement(0));
     have av == a_vec.0[3];
     have av == old((bytes[3] as u32)) by { rewrite(av, a_vec.0[3]); known(); }
     have to_integer(av) <= 255;
     have to_integer(a) + to_integer(av) <= 4294967295 by solve() using { to_integer(a) <= 766; to_integer(av) <= 255; };
     mark sum_a_3;
     apply(integer::uint32_add_to_integer(at(sum_a_3, a), at(sum_a_3, av)));
     step_until(assignment(a, 1)); step();
     have a == at(sum_a_3, a) + at(sum_a_3, av);
     have a == ((((1u32 + old((bytes[0] as u32))) + old((bytes[1] as u32))) + old((bytes[2] as u32))) + old((bytes[3] as u32)));
     step_until(loop(4));
     step_until(loop(4));
     have b == 4u32;
     have to_integer(b) <= 4;
     step_until(loop(4).statement(0));
     have bv == b_vec.0[0];
     have bv == (old((bytes[0] as u32)) * 4u32);
     have to_integer(bv) <= 262080;
     have to_integer(b) + to_integer(bv) <= 4294967295 by solve() using { to_integer(b) <= 4; to_integer(bv) <= 262080; };
     mark sum_b_0;
     apply(integer::uint32_add_to_integer(at(sum_b_0, b), at(sum_b_0, bv)));
     step_until(assignment(b, 5)); step();
     have b == at(sum_b_0, b) + at(sum_b_0, bv);
     have b == (4u32 + (old((bytes[0] as u32)) * 4u32));
     have to_integer(b) == to_integer(at(sum_b_0, b)) + to_integer(at(sum_b_0, bv)) by { known(); }
     have to_integer(b) <= 262084 by {
      solve() using { to_integer(b) == to_integer(at(sum_b_0, b)) + to_integer(at(sum_b_0, bv)); to_integer(at(sum_b_0, b)) <= 4; to_integer(at(sum_b_0, bv)) <= 262080; };
     }
     step(); step();
     step_until(loop(4).statement(0));
     have bv == b_vec.0[1];
     have bv == ((old((bytes[1] as u32)) * 4u32) + (65521u32 - old((bytes[1] as u32))));
     have to_integer(bv) <= 327601;
     have to_integer(b) + to_integer(bv) <= 4294967295 by solve() using { to_integer(b) <= 262084; to_integer(bv) <= 327601; };
     mark sum_b_1;
     apply(integer::uint32_add_to_integer(at(sum_b_1, b), at(sum_b_1, bv)));
     step_until(assignment(b, 5)); step();
     have b == at(sum_b_1, b) + at(sum_b_1, bv);
     have b == ((4u32 + (old((bytes[0] as u32)) * 4u32)) + ((old((bytes[1] as u32)) * 4u32) + (65521u32 - old((bytes[1] as u32)))));
     have to_integer(b) == to_integer(at(sum_b_1, b)) + to_integer(at(sum_b_1, bv)) by { known(); }
     have to_integer(b) <= 589685 by {
      solve() using { to_integer(b) == to_integer(at(sum_b_1, b)) + to_integer(at(sum_b_1, bv)); to_integer(at(sum_b_1, b)) <= 262084; to_integer(at(sum_b_1, bv)) <= 327601; };
     }
     step(); step();
     step_until(loop(4).statement(0));
     have bv == b_vec.0[2];
     have bv == ((old((bytes[2] as u32)) * 4u32) + ((65521u32 - old((bytes[2] as u32))) * 2u32));
     have to_integer(bv) <= 393122;
     have to_integer(b) + to_integer(bv) <= 4294967295 by solve() using { to_integer(b) <= 589685; to_integer(bv) <= 393122; };
     mark sum_b_2;
     apply(integer::uint32_add_to_integer(at(sum_b_2, b), at(sum_b_2, bv)));
     step_until(assignment(b, 5)); step();
     have b == at(sum_b_2, b) + at(sum_b_2, bv);
     have b == (((4u32 + (old((bytes[0] as u32)) * 4u32)) + ((old((bytes[1] as u32)) * 4u32) + (65521u32 - old((bytes[1] as u32))))) + ((old((bytes[2] as u32)) * 4u32) + ((65521u32 - old((bytes[2] as u32))) * 2u32)));
     have to_integer(b) == to_integer(at(sum_b_2, b)) + to_integer(at(sum_b_2, bv)) by { known(); }
     have to_integer(b) <= 982807 by {
      solve() using { to_integer(b) == to_integer(at(sum_b_2, b)) + to_integer(at(sum_b_2, bv)); to_integer(at(sum_b_2, b)) <= 589685; to_integer(at(sum_b_2, bv)) <= 393122; };
     }
     step(); step();
     step_until(loop(4).statement(0));
     have bv == b_vec.0[3];
     have bv == ((old((bytes[3] as u32)) * 4u32) + ((65521u32 - old((bytes[3] as u32))) * 3u32));
     have to_integer(bv) <= 458643;
     have to_integer(b) + to_integer(bv) <= 4294967295 by solve() using { to_integer(b) <= 982807; to_integer(bv) <= 458643; };
     mark sum_b_3;
     apply(integer::uint32_add_to_integer(at(sum_b_3, b), at(sum_b_3, bv)));
     step_until(assignment(b, 5)); step();
     have b == at(sum_b_3, b) + at(sum_b_3, bv);
     have b == ((((4u32 + (old((bytes[0] as u32)) * 4u32)) + ((old((bytes[1] as u32)) * 4u32) + (65521u32 - old((bytes[1] as u32))))) + ((old((bytes[2] as u32)) * 4u32) + ((65521u32 - old((bytes[2] as u32))) * 2u32))) + ((old((bytes[3] as u32)) * 4u32) + ((65521u32 - old((bytes[3] as u32))) * 3u32)));
     step_until(loop(5));
     have remainder.len() == 0u64;
     step_until(statement(22));
     mark output_a;
     have at(output_a, a) == ((((1u32 + (old((bytes[0] as u32)))) + (old((bytes[1] as u32)))) + (old((bytes[2] as u32)))) + (old((bytes[3] as u32)))) by solve() using { a == ((((1u32 + (old((bytes[0] as u32)))) + (old((bytes[1] as u32)))) + (old((bytes[2] as u32)))) + (old((bytes[3] as u32)))); };
     have (at(output_a, a) % 65521u32) == (((((1u32 + (old((bytes[0] as u32)))) + (old((bytes[1] as u32)))) + (old((bytes[2] as u32)))) + (old((bytes[3] as u32))))) % 65521u32 by { rewrite(at(output_a, a), ((((1u32 + (old((bytes[0] as u32)))) + (old((bytes[1] as u32)))) + (old((bytes[2] as u32)))) + (old((bytes[3] as u32))))); solve(); }
     have (at(output_a, a)) % 65521u32 < 65521u32;
     have 0 <= to_integer((at(output_a, a) % 65521u32));
     have to_integer((at(output_a, a) % 65521u32)) <= 4294967295;
     have to_integer((at(output_a, a) % 65521u32)) < to_integer(65521u32);
     have to_integer((at(output_a, a) % 65521u32)) <= 65535 by solve() using { to_integer((at(output_a, a) % 65521u32)) < 65521; };
     step_until(statement(23));
     mark output_b;
     have at(output_b, b) == ((((4u32 + (old((bytes[0] as u32)) * 4u32)) + (old((bytes[1] as u32)) * 4u32 + (65521u32 - old((bytes[1] as u32))))) + (old((bytes[2] as u32)) * 4u32 + ((65521u32 - old((bytes[2] as u32))) * 2u32))) + (old((bytes[3] as u32)) * 4u32 + ((65521u32 - old((bytes[3] as u32))) * 3u32))) by solve() using { b == ((((4u32 + (old((bytes[0] as u32)) * 4u32)) + (old((bytes[1] as u32)) * 4u32 + (65521u32 - old((bytes[1] as u32))))) + (old((bytes[2] as u32)) * 4u32 + ((65521u32 - old((bytes[2] as u32))) * 2u32))) + (old((bytes[3] as u32)) * 4u32 + ((65521u32 - old((bytes[3] as u32))) * 3u32))); };
     have (at(output_b, b) % 65521u32) == (((((4u32 + (old((bytes[0] as u32)) * 4u32)) + (old((bytes[1] as u32)) * 4u32 + (65521u32 - old((bytes[1] as u32))))) + (old((bytes[2] as u32)) * 4u32 + ((65521u32 - old((bytes[2] as u32))) * 2u32))) + (old((bytes[3] as u32)) * 4u32 + ((65521u32 - old((bytes[3] as u32))) * 3u32)))) % 65521u32 by { rewrite(at(output_b, b), ((((4u32 + (old((bytes[0] as u32)) * 4u32)) + (old((bytes[1] as u32)) * 4u32 + (65521u32 - old((bytes[1] as u32))))) + (old((bytes[2] as u32)) * 4u32 + ((65521u32 - old((bytes[2] as u32))) * 2u32))) + (old((bytes[3] as u32)) * 4u32 + ((65521u32 - old((bytes[3] as u32))) * 3u32)))); solve(); }
     have (at(output_b, b)) % 65521u32 < 65521u32;
     have 0 <= to_integer((at(output_b, b) % 65521u32));
     have to_integer((at(output_b, b) % 65521u32)) <= 4294967295;
     have to_integer((at(output_b, b) % 65521u32)) < to_integer(65521u32);
     have to_integer((at(output_b, b) % 65521u32)) <= 65535 by solve() using { to_integer((at(output_b, b) % 65521u32)) < 65521; };
     step_until(function.exit);
     have statement(22).call(0).result == 65521u32 by known();
     have self.a == ((at(output_a, a) % statement(22).call(0).result) as u16) by known();
     have self.a == ((at(output_a, a) % 65521u32) as u16) by { rewrite(self.a, ((at(output_a, a) % statement(22).call(0).result) as u16)); rewrite(statement(22).call(0).result, 65521u32); known(); }
     have to_integer(self.a) == to_integer((at(output_a, a) % 65521u32)) by { rewrite(self.a, ((at(output_a, a) % 65521u32) as u16)); solve() using { 0 <= to_integer((at(output_a, a) % 65521u32)); to_integer((at(output_a, a) % 65521u32)) <= 65535; }; }
     have statement(23).call(0).result == 65521u32 by known();
     have self.b == ((at(output_b, b) % statement(23).call(0).result) as u16) by known();
     have self.b == ((at(output_b, b) % 65521u32) as u16) by { rewrite(self.b, ((at(output_b, b) % statement(23).call(0).result) as u16)); rewrite(statement(23).call(0).result, 65521u32); known(); }
     have to_integer(self.b) == to_integer((at(output_b, b) % 65521u32)) by { rewrite(self.b, ((at(output_b, b) % 65521u32) as u16)); solve() using { 0 <= to_integer((at(output_b, b) % 65521u32)); to_integer((at(output_b, b) % 65521u32)) <= 65535; }; }
     have bytes[0] == old(bytes[0]) by solve() using {};
     have bytes[1] == old(bytes[1]) by solve() using {};
     have bytes[2] == old(bytes[2]) by solve() using {};
     have bytes[3] == old(bytes[3]) by solve() using {};
     have to_integer(self.a) == to_integer((((((1u32 + (old((bytes[0] as u32)))) + (old((bytes[1] as u32)))) + (old((bytes[2] as u32)))) + (old((bytes[3] as u32))))) % 65521u32) by {
      rewrite(to_integer(self.a), to_integer((at(output_a, a) % 65521u32)));
      rewrite((at(output_a, a) % 65521u32), (((((1u32 + (old((bytes[0] as u32)))) + (old((bytes[1] as u32)))) + (old((bytes[2] as u32)))) + (old((bytes[3] as u32))))) % 65521u32); normalize();
     }
     have to_integer((((((1u32 + (old((bytes[0] as u32)))) + (old((bytes[1] as u32)))) + (old((bytes[2] as u32)))) + (old((bytes[3] as u32))))) % 65521u32) == old(adler_spec_a(bytes, 4, 1)) by known();
     have to_integer(self.a) == old(adler_spec_a(bytes, 4, 1)) by {
      rewrite(to_integer(self.a), to_integer((((((1u32 + (old((bytes[0] as u32)))) + (old((bytes[1] as u32)))) + (old((bytes[2] as u32)))) + (old((bytes[3] as u32))))) % 65521u32)); known();
     }
     have to_integer(self.b) == to_integer((((((4u32 + (old((bytes[0] as u32)) * 4u32)) + (old((bytes[1] as u32)) * 4u32 + (65521u32 - old((bytes[1] as u32))))) + (old((bytes[2] as u32)) * 4u32 + ((65521u32 - old((bytes[2] as u32))) * 2u32))) + (old((bytes[3] as u32)) * 4u32 + ((65521u32 - old((bytes[3] as u32))) * 3u32)))) % 65521u32) by {
      rewrite(to_integer(self.b), to_integer((at(output_b, b) % 65521u32)));
      rewrite((at(output_b, b) % 65521u32), (((((4u32 + (old((bytes[0] as u32)) * 4u32)) + (old((bytes[1] as u32)) * 4u32 + (65521u32 - old((bytes[1] as u32))))) + (old((bytes[2] as u32)) * 4u32 + ((65521u32 - old((bytes[2] as u32))) * 2u32))) + (old((bytes[3] as u32)) * 4u32 + ((65521u32 - old((bytes[3] as u32))) * 3u32)))) % 65521u32); normalize();
     }
     have to_integer((((((4u32 + (old((bytes[0] as u32)) * 4u32)) + (old((bytes[1] as u32)) * 4u32 + (65521u32 - old((bytes[1] as u32))))) + (old((bytes[2] as u32)) * 4u32 + ((65521u32 - old((bytes[2] as u32))) * 2u32))) + (old((bytes[3] as u32)) * 4u32 + ((65521u32 - old((bytes[3] as u32))) * 3u32)))) % 65521u32) == old(adler_spec_b(bytes, 4, 1, 0)) by known();
     have to_integer(self.b) == old(adler_spec_b(bytes, 4, 1, 0)) by {
      rewrite(to_integer(self.b), to_integer((((((4u32 + (old((bytes[0] as u32)) * 4u32)) + (old((bytes[1] as u32)) * 4u32 + (65521u32 - old((bytes[1] as u32))))) + (old((bytes[2] as u32)) * 4u32 + ((65521u32 - old((bytes[2] as u32))) * 2u32))) + (old((bytes[3] as u32)) * 4u32 + ((65521u32 - old((bytes[3] as u32))) * 3u32)))) % 65521u32)); known();
     }
     // Close the owned fields and the checked output equalities.
     known();
     known(); known(); known(); known();
     known();
     known();
     known();
     known();
     known();
    }
}
