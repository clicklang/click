import click::integer;
import click::rust::slice;

// Original compute bounds for every small-batch length and canonical seeds.
// Length is at most 22207 bytes; both initial fields are below MOD = 65521.
// The stored vector and scalar iterators supply their actual remaining state.
// Full outer batches and final checksum postconditions remain separate work.
// Verification assembles this contract with checked helpers and arithmetic libraries.

theorem adler_uint64_self_subtract(n: uint64) { ensures n - n == 0u64 by close(); }
theorem adler_i32_below_mod(n: int32) { requires n <= 65520; ensures n < 65521 by close() using { n <= 65520; }; }
theorem adler_bounded_pointer_association(base: const uint8*, index: int32) {
 requires 0 <= index;
 requires index <= 22200;
 ensures (base + index) + 4 == base + (index + 4) by {
  have defined(index + 4) by close() using { 0 <= index; index <= 22200; };
  apply(integer::uint8_pointer_add_associate_int32(base, index, 4));
 }
}
theorem adler_scalar_batch_product_bound(length: uint32, seed: uint32) {
 requires length <= 22204u32;
 requires seed <= 65520u32;
 ensures to_integer(length) * to_integer(seed) <= 1454806080 by {
  have 0 <= to_integer(length);
  have to_integer(length) <= 4294967295;
  have 0 <= to_integer(seed);
  have to_integer(seed) <= 4294967295;
  close() using { 0 <= to_integer(length); to_integer(length) <= 22204; 0 <= to_integer(seed); to_integer(seed) <= 65520; };
 }
}
theorem adler_small_length_cast(length: uint64) {
 requires length <= 22204u64;
 ensures (length as u32) <= 22204u32 and to_integer((length as u32)) == to_integer(length) by {
  have 0u64 <= length by close();
  have 0 <= to_integer(length) by close();
  have to_integer(length) <= 4294967295 by close() using { to_integer(length) <= 22204; };
  have to_integer((length as u32)) == to_integer(length) by {
   close() using { 0 <= to_integer(length); to_integer(length) <= 4294967295; };
  }
  have to_integer((length as u32)) <= to_integer(22204u32) by { rewrite(to_integer((length as u32)), to_integer(length)); close(); }
  close();
 }
}



theorem adler_tail_pointer_association(base: const uint8*, index: int32) {
 requires 0 <= index;
 requires index <= 22206;
 ensures (base + index) + 1 == base + (index + 1) by {
  have defined(index + 1) by close() using { 0 <= index; index <= 22206; };
  apply(integer::uint8_pointer_add_associate_int32(base, index, 1));
 }
}

// The remainder chunk loop counts whole four-byte chunks (`iter.len()`); the lane
// lemmas count remaining bytes. `adler_chunk_bytes` names that byte count.
function adler_chunk_bytes(count: uint64) -> uint64 { count * 4u64 }

theorem adler_chunk_bytes_value(count: uint64) {
 requires count <= 5551u64;
 ensures to_integer(adler_chunk_bytes(count)) == to_integer(count) * 4 by {
  unfold(adler_chunk_bytes(count));
  close();
 }
}
theorem adler_quarter_exact(p: uint64) {
 requires p % 4u64 == 0u64;
 ensures to_integer(p / 4u64) * 4 == to_integer(p) by {
  apply(integer::uint64_divide_to_integer(p, 4u64));
  apply(integer::uint64_remainder_to_integer(p, 4u64));
  apply(integer::truncation_identity(to_integer(p), 4));
  have to_integer(p % 4u64) == 0;
  close();
 }
}
theorem adler_chunk_bytes_initial(p: uint64) {
 requires p % 4u64 == 0u64;
 requires to_integer(p) <= 22204;
 ensures adler_chunk_bytes(p / 4u64) == p by {
  apply(adler_quarter_exact(p));
  have to_integer(p / 4u64) <= 5551;
  have p / 4u64 <= 5551u64;
  apply(adler_chunk_bytes_value(p / 4u64));
  have to_integer(adler_chunk_bytes(p / 4u64)) == to_integer(p);
  close();
 }
}
theorem adler_chunk_bytes_step(count: uint64) {
 requires 0u64 < count;
 requires count <= 5551u64;
 ensures 4u64 <= adler_chunk_bytes(count) by {
  apply(adler_chunk_bytes_value(count));
  have 4 <= to_integer(adler_chunk_bytes(count));
  close();
 }
 ensures adler_chunk_bytes(count - 1u64) == adler_chunk_bytes(count) - 4u64 by {
  apply(adler_chunk_bytes_value(count));
  have to_integer(count - 1u64) == to_integer(count) - 1;
  have to_integer(count - 1u64) <= to_integer(5551u64);
  apply(adler_chunk_bytes_value(count - 1u64));
  close();
 }
}
theorem adler_chunk_bytes_zero() {
 ensures adler_chunk_bytes(0u64) == 0u64 by { unfold(adler_chunk_bytes(0u64)); close(); }
}
theorem adler_chunk_bytes_position(p: uint64, count: uint64) {
 requires p % 4u64 == 0u64;
 requires to_integer(p) <= 22204;
 requires count <= p / 4u64;
 ensures to_integer((p / 4u64 - count) * 4u64) == to_integer(p - adler_chunk_bytes(count)) by {
  apply(adler_quarter_exact(p));
  have to_integer(p / 4u64) <= 5551;
  have count <= 5551u64;
  apply(adler_chunk_bytes_value(count));
  have to_integer(p / 4u64 - count) == to_integer(p / 4u64) - to_integer(count);
  have to_integer((p / 4u64 - count) * 4u64) == to_integer(p / 4u64 - count) * 4;
  have to_integer(p - adler_chunk_bytes(count)) == to_integer(p) - to_integer(adler_chunk_bytes(count));
  close();
 }
}
theorem adler_small_outer_quotient(n: uint64) {
 requires to_integer(n) <= 22204;
 ensures n / 22208u64 == 0u64 by {
  have 0 <= to_integer(n);
  have 0 * 22208 <= to_integer(n);
  have to_integer(n) < 1 * 22208;
  apply(integer::positive_divisor_quotient_lower(to_integer(n), 22208, 0));
  apply(integer::positive_divisor_quotient_strict_upper(to_integer(n), 22208, 1));
  apply(integer::uint64_divide_to_integer(n, 22208u64));
  have to_integer(n / 22208u64) == 0;
  close();
 }
}
theorem adler_remainder_chunk_step(p: uint64, count: uint64, passes: Integer) {
 requires p % 4u64 == 0u64;
 requires to_integer(p) <= 22204;
 requires 0u64 < count;
 requires 0 <= passes;
 requires to_integer(count) + passes == to_integer(p / 4u64);
 ensures count <= p / 4u64 by close();
 ensures to_integer(p / 4u64 - count) == passes by {
  have count <= p / 4u64;
  have to_integer(p / 4u64 - count) == to_integer(p / 4u64) - to_integer(count);
  close();
 }
 ensures to_integer(p / 4u64 - count) == passes + to_integer(0u64) by {
  have count <= p / 4u64;
  have to_integer(p / 4u64 - count) == to_integer(p / 4u64) - to_integer(count);
  close();
 }
 ensures p / 4u64 - count < p / 4u64 by {
  have count <= p / 4u64;
  have to_integer(p / 4u64 - count) == to_integer(p / 4u64) - to_integer(count);
  have to_integer(p / 4u64 - count) < to_integer(p / 4u64);
  close();
 }
 ensures to_integer(p / 4u64 - count) < to_integer(p / 4u64) by {
  have count <= p / 4u64;
  have to_integer(p / 4u64 - count) == to_integer(p / 4u64) - to_integer(count);
  close();
 }
 ensures count <= 5551u64 by {
  apply(adler_quarter_exact(p));
  have to_integer(p / 4u64) <= 5551;
  close();
 }
 ensures to_integer((p / 4u64 - count) * 4u64) < to_integer(p) by {
  apply(adler_quarter_exact(p));
  have count <= p / 4u64;
  have to_integer(p / 4u64) <= 5551;
  have to_integer(p / 4u64 - count) == to_integer(p / 4u64) - to_integer(count);
  have to_integer((p / 4u64 - count) * 4u64) == to_integer(p / 4u64 - count) * 4;
  close();
 }
 ensures to_integer((p / 4u64 - count) * 4u64 + 3u64) < to_integer(p) by {
  apply(adler_quarter_exact(p));
  have count <= p / 4u64;
  have to_integer(p / 4u64) <= 5551;
  have to_integer(p / 4u64 - count) == to_integer(p / 4u64) - to_integer(count);
  have to_integer((p / 4u64 - count) * 4u64) == to_integer(p / 4u64 - count) * 4;
  have to_integer((p / 4u64 - count) * 4u64 + 3u64) == to_integer((p / 4u64 - count) * 4u64) + 3;
  close();
 }
}
theorem adler_chunk_bytes_next(count: uint64, next: uint64) {
 requires 0u64 < count;
 requires count <= 5551u64;
 requires to_integer(next) == to_integer(count) - 1;
 ensures to_integer(adler_chunk_bytes(next)) == to_integer(adler_chunk_bytes(count)) - 4 by {
  apply(adler_chunk_bytes_value(count));
  have next <= 5551u64;
  apply(adler_chunk_bytes_value(next));
  close();
 }
}
theorem adler_uint64_pointer_association(base: const uint8*, p: uint64, q: uint64) {
 requires to_integer(p) + to_integer(q) <= 18446744073709551615;
 ensures (base + p) + q == base + (p + q) by {
  apply(integer::uint64_add_to_integer(p, q));
  close() using { to_integer(p + q) == to_integer(p) + to_integer(q); };
 }
}
theorem adler_tail_pointer_position(base: const uint8*, p: uint64, n: uint64, r: uint64) {
 requires to_integer(p) <= to_integer(n);
 requires to_integer(r) <= to_integer(n - p);
 ensures (base + p) + ((n - p) - r) == base + (n - r) by {
  have to_integer(n - p) == to_integer(n) - to_integer(p);
  have to_integer((n - p) - r) == to_integer(n - p) - to_integer(r);
  have to_integer(r) <= to_integer(n);
  have to_integer(n - r) == to_integer(n) - to_integer(r);
  have to_integer(p + ((n - p) - r)) == to_integer(p) + to_integer((n - p) - r);
  have to_integer(p + ((n - p) - r)) == to_integer(n - r);
  have to_integer(p) + to_integer((n - p) - r) <= 18446744073709551615;
  apply(adler_uint64_pointer_association(base, p, (n - p) - r));
  rewrite((base + p) + ((n - p) - r), base + (p + ((n - p) - r)));
  close() using { to_integer(p + ((n - p) - r)) == to_integer(n - r); };
 }
}
theorem adler_tail_read_offset(p: uint64, n: uint64, length: uint64, r: uint64) {
 requires to_integer(p) <= to_integer(n);
 requires to_integer(length) == to_integer(n - p);
 requires 1u64 <= r;
 requires r <= length;
 ensures to_integer(p + (length - r)) < to_integer(n) by {
  have to_integer(n - p) == to_integer(n) - to_integer(p);
  have to_integer(length - r) == to_integer(length) - to_integer(r);
  have to_integer(p) + to_integer(length - r) <= 18446744073709551615;
  apply(integer::uint64_add_to_integer(p, length - r));
  close();
 }
}

impl adler2::Adler32 {
    fn compute(&mut self, bytes: &[u8]) {
     requires bytes.len() <= 22207u64;
     requires bytes.len() < 22208u64;
     requires (self.a as u32) <= 65520u32;
     requires (self.b as u32) <= 65520u32;
     owns self.a;
     owns self.b;
     views *bytes;
     ensures self.a < 65521;
     ensures self.b < 65521;
     ensures to_integer(self.a) == old(adler_spec_a(bytes, ((bytes.len() as u32) as i32), old(to_integer((self.a as u32)))));
     ensures to_integer(self.b) == old(adler_spec_b(bytes, ((bytes.len() as u32) as i32), old(to_integer((self.a as u32))), old(to_integer((self.b as u32)))));
    } by {
     apply(adler_signed_small_prefix(bytes.len()));
     apply(adler_small_prefix_divisible(bytes.len()));
     apply(adler_native_small_prefix_divisible(bytes.len()));
     apply(adler_small_native_prefix(bytes.len()));
     apply(adler_small_tail_metadata(bytes.len()));
     apply(adler_small_signed_tail(bytes.len()));
     apply(adler_signed_partition_identity(bytes.len()));
     have bytes.len() % 4u64 <= bytes.len() by normalize();
     have bytes.len() - bytes.len() % 4u64 <= bytes.len();
     apply(adler_small_outer_remainder(bytes.len() - bytes.len() % 4u64));
     have bytes.len() <= 2147483647u64 by normalize() using { bytes.len() <= 22207u64; };
     have 0 <= old((((bytes.len() - bytes.len() % 4u64) as u32) as i32)) by close() using { 0 <= (((bytes.len() - bytes.len() % 4u64) as u32) as i32); };
     have old((((bytes.len() - bytes.len() % 4u64) as u32) as i32)) <= 22204 by close() using { (((bytes.len() - bytes.len() % 4u64) as u32) as i32) <= 22204; };
     have old((((bytes.len() - bytes.len() % 4u64) as u32) as i32)) % 4 == 0 by close() using { (((bytes.len() - bytes.len() % 4u64) as u32) as i32) % 4 == 0; };
     have bytes.len() % 4u64 <= bytes.len() by normalize();
     have bytes.len() - bytes.len() % 4u64 <= bytes.len();
     have bytes.len() - bytes.len() % 4u64 <= 2147483647u64 by close() using { bytes.len() - bytes.len() % 4u64 <= bytes.len(); bytes.len() <= 2147483647u64; };
     have to_integer((bytes.len())) <= to_integer(22207u64);
     have bytes.len() < 22208u64 by close();
     step_until(assignment(b, 0).entry); step();
     have a == old((self.a as u32));
     have a <= 65520u32 by { rewrite(a, old((self.a as u32))); close(); }
     have b == old((self.b as u32));
     have b <= 65520u32 by { rewrite(b, old((self.b as u32))); close(); }
     step_until(assignment(remainder_chunk_len, 0).entry); step();
     have chunk_iter == chunks_exact::chunks_exact(Slice<u8>::Slice(bytes, bytes.len() - bytes.len() % 4u64), 22208u64);
     have remainder_chunk_len == (bytes.len() - bytes.len() % 4u64) % 22208u64 by {
      apply(chunks_exact::remainder_chunks_exact(Slice<u8>::Slice(bytes, bytes.len() - bytes.len() % 4u64), 22208u64));
      close();
     }
     have remainder_chunk == bytes + ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) by {
      apply(chunks_exact::remainder_chunks_exact(Slice<u8>::Slice(bytes, bytes.len() - bytes.len() % 4u64), 22208u64));
      close();
     }
     have ((remainder_chunk_len as u32) as i32) == old((((bytes.len() - bytes.len() % 4u64) as u32) as i32));
     step_until(loop(0).entry);
     have loop(0).iter == chunks_exact::chunks_exact(Slice<u8>::Slice(bytes, bytes.len() - bytes.len() % 4u64), 22208u64);
     have (bytes.len() - bytes.len() % 4u64) / 22208u64 == 0u64 by { apply(adler_small_outer_quotient(bytes.len() - bytes.len() % 4u64)); }
     have loop(0).iter.len() == 0u64 by {
      apply(chunks_exact::len_chunks_exact(Slice<u8>::Slice(bytes, bytes.len() - bytes.len() % 4u64), 22208u64));
      close();
     }
     have to_integer(remainder_chunk_len) == to_integer(bytes.len() - bytes.len() % 4u64) by { rewrite(remainder_chunk_len, (bytes.len() - bytes.len() % 4u64) % 22208u64); close(); }
     have to_integer(bytes.len() - bytes.len() % 4u64) == to_integer(bytes.len()) - to_integer(bytes.len() % 4u64);
     have remainder_chunk_len == bytes.len() - bytes.len() % 4u64;
     have to_integer((bytes.len())) <= to_integer(2147483647u64);

     have to_integer((bytes.len() - bytes.len() % 4u64)) <= to_integer(2147483647u64);
     have to_integer(remainder_chunk_len) <= to_integer(2147483647u64) by { rewrite(to_integer(remainder_chunk_len), to_integer(bytes.len() - bytes.len() % 4u64)); close(); }
     have remainder_chunk_len <= 2147483647u64;
     have remainder_chunk == bytes by { rewrite(remainder_chunk, bytes + ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64)); rewrite((bytes.len() - bytes.len() % 4u64) % 22208u64, bytes.len() - bytes.len() % 4u64); apply(adler_uint64_self_subtract(bytes.len() - bytes.len() % 4u64)); close(); }
     step_until(loop(2).entry);
     have loop(2).iter == chunks_exact::chunks_exact(Slice<u8>::Slice(bytes, bytes.len() - bytes.len() % 4u64), 4u64);
     have loop(2).iter.len() == (bytes.len() - bytes.len() % 4u64) / 4u64 by {
      apply(chunks_exact::len_chunks_exact(Slice<u8>::Slice(bytes, bytes.len() - bytes.len() % 4u64), 4u64));
      close();
     }
     apply(chunks_exact::after_zero(chunks_exact::chunks_exact(Slice<u8>::Slice(bytes, bytes.len() - bytes.len() % 4u64), 4u64)));
     have loop(2).iter == chunks_exact::after(chunks_exact::chunks_exact(Slice<u8>::Slice(bytes, bytes.len() - bytes.len() % 4u64), 4u64), 0);
     have adler_chunk_bytes(loop(2).iter.len()) == bytes.len() - bytes.len() % 4u64 by {
      apply(adler_chunk_bytes_initial(bytes.len() - bytes.len() % 4u64));
      rewrite(loop(2).iter.len(), (bytes.len() - bytes.len() % 4u64) / 4u64);
      close();
     }
     have ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32) == old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)) by { rewrite(adler_chunk_bytes(loop(2).iter.len()), bytes.len() - bytes.len() % 4u64); close(); }
     have bytes == old(bytes);
     apply(adler_lane_initial_ceiling());
     apply(adler_lane_iterator_initial(old((((bytes.len() - bytes.len() % 4u64) as u32) as i32))));
     have adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32)) == 0 by { rewrite(((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32), old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32))); close(); }
     have to_integer(a_vec.0[0]) == 0;
     have to_integer(a_vec.0[0]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32))) by { rewrite(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32)), 0); rewrite(adler_lane_a_ceiling(0), 65520); close() using { to_integer(a_vec.0[0]) == 0; }; }
     have to_integer(b_vec.0[0]) == 0;
     have to_integer(b_vec.0[0]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32))) by { rewrite(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32)), 0); rewrite(adler_lane_b_ceiling(0), 65520); close() using { to_integer(b_vec.0[0]) == 0; }; }
     have to_integer(a_vec.0[1]) == 0;
     have to_integer(a_vec.0[1]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32))) by { rewrite(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32)), 0); rewrite(adler_lane_a_ceiling(0), 65520); close() using { to_integer(a_vec.0[1]) == 0; }; }
     have to_integer(b_vec.0[1]) == 0;
     have to_integer(b_vec.0[1]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32))) by { rewrite(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32)), 0); rewrite(adler_lane_b_ceiling(0), 65520); close() using { to_integer(b_vec.0[1]) == 0; }; }
     have to_integer(a_vec.0[2]) == 0;
     have to_integer(a_vec.0[2]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32))) by { rewrite(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32)), 0); rewrite(adler_lane_a_ceiling(0), 65520); close() using { to_integer(a_vec.0[2]) == 0; }; }
     have to_integer(b_vec.0[2]) == 0;
     have to_integer(b_vec.0[2]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32))) by { rewrite(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32)), 0); rewrite(adler_lane_b_ceiling(0), 65520); close() using { to_integer(b_vec.0[2]) == 0; }; }
     have to_integer(a_vec.0[3]) == 0;
     have to_integer(a_vec.0[3]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32))) by { rewrite(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32)), 0); rewrite(adler_lane_a_ceiling(0), 65520); close() using { to_integer(a_vec.0[3]) == 0; }; }
     have to_integer(b_vec.0[3]) == 0;
     have to_integer(b_vec.0[3]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32))) by { rewrite(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32)), 0); rewrite(adler_lane_b_ceiling(0), 65520); close() using { to_integer(b_vec.0[3]) == 0; }; }
     have 0 <= ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32) by { rewrite(((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32), old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32))); close(); }
     have ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32) <= old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)) by { rewrite(((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32), old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32))); normalize() using {}; }
     have 0 <= ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32) and ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32) <= old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)) by close();
     have ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32) % 4 == 0 by { rewrite(((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32), old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32))); close(); }
     have adler_chunk_bytes(loop(2).iter.len()) <= bytes.len() - bytes.len() % 4u64 by { rewrite(adler_chunk_bytes(loop(2).iter.len()), bytes.len() - bytes.len() % 4u64); normalize(); }
     have adler_chunk_bytes(loop(2).iter.len()) % 4u64 == 0u64 by { rewrite(adler_chunk_bytes(loop(2).iter.len()), bytes.len() - bytes.len() % 4u64); close(); }
     have (bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(loop(2).iter.len()) == 0u64 by close() using { adler_chunk_bytes(loop(2).iter.len()) == bytes.len() - bytes.len() % 4u64; };
     have bytes.len() < 22208u64 by close();
     have bytes.len() == old(bytes.len()) by close();
     have 0 <= to_integer(a);
     have to_integer(a) <= 4294967295;
     have to_integer(a) <= to_integer(65520u32);
     apply(adler_spec_empty(bytes, to_integer(a), 0));
     have ((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32)) == 0 by { rewrite(((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32), (((bytes.len() - bytes.len() % 4u64) as uint32) as int32)); normalize(); }
     have adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])) == to_integer(a) by { unfold(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]))); close(); }
     have to_integer(a) == 0 * 65521 + to_integer(a) by close() using {};
     apply(adler_residue_unique(to_integer(a), 0, to_integer(a)));
     have truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521) == adler_spec_a(bytes, ((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32)), to_integer(a)) by { rewrite(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32)), 0); rewrite(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), to_integer(a)); close() using { truncating_remainder(to_integer(a), 65521) == to_integer(a); adler_spec_a(bytes, 0, to_integer(a)) == to_integer(a); }; }
     have 0 <= to_integer(b);
     have to_integer(b) <= 4294967295;
     have to_integer(b) <= to_integer(65520u32);
     apply(adler_spec_empty(bytes, to_integer(a), to_integer(b)));
     have to_integer(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32))) == 0 by close() using { ((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32)) == 0; };
     have adler_lane_b(to_integer(b) + to_integer(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])) == to_integer(b) + 393126 by { rewrite(to_integer(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32))), 0); unfold(adler_lane_b(to_integer(b) + 0 * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3]))); close() using { to_integer(a_vec.0[1]) == 0; to_integer(a_vec.0[2]) == 0; to_integer(a_vec.0[3]) == 0; to_integer(b_vec.0[0]) == 0; to_integer(b_vec.0[1]) == 0; to_integer(b_vec.0[2]) == 0; to_integer(b_vec.0[3]) == 0; }; }
     have 0 <= to_integer(b) + 393126 by close() using { 0 <= to_integer(b); };
     have 0 <= adler_lane_b(to_integer(b) + to_integer(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])) by { rewrite(adler_lane_b(to_integer(b) + to_integer(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), to_integer(b) + 393126); close(); }
     have to_integer(b) + 393126 == 6 * 65521 + to_integer(b) by close() using {};
     apply(adler_residue_unique(to_integer(b) + 393126, 6, to_integer(b)));
     have truncating_remainder(adler_lane_b(to_integer(b) + to_integer(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), 65521) == adler_spec_b(bytes, ((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32)), to_integer(a), to_integer(b)) by { rewrite(adler_lane_b(to_integer(b) + to_integer(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), to_integer(b) + 393126); rewrite(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32)), 0); close() using { truncating_remainder(to_integer(b) + 393126, 65521) == to_integer(b); adler_spec_b(bytes, 0, to_integer(a), to_integer(b)) == to_integer(b); }; }
     have defined(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)) - (((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32)));
     loop {
      decreases iter.len();
      owns a_vec.0[0..4];
      owns b_vec.0[0..4];
      views *bytes;
      invariant bytes.len() <= 22207u64;
      invariant bytes.len() < 22208u64;
      invariant bytes.len() - bytes.len() % 4u64 <= 22204u64;
      invariant bytes == old(bytes);
      invariant forall (k: int32) { 0 <= k and k < ((bytes.len() as u32) as i32) implies bytes[k] == old(bytes[k]) };
      invariant bytes.len() == old(bytes.len());
      invariant a <= 65520u32;
      invariant b <= 65520u32;
      invariant 0 <= old((((bytes.len() - bytes.len() % 4u64) as u32) as i32));
      invariant old((((bytes.len() - bytes.len() % 4u64) as u32) as i32)) <= 22204;
      invariant old((((bytes.len() - bytes.len() % 4u64) as u32) as i32)) % 4 == 0;
      invariant 0 <= ((adler_chunk_bytes(iter.len()) as uint32) as int32) and ((adler_chunk_bytes(iter.len()) as uint32) as int32) <= old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32));
      invariant truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521) == adler_spec_a(bytes, ((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)), to_integer(a));
      invariant 0 <= adler_lane_b(to_integer(b) + to_integer(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3]));
      invariant truncating_remainder(adler_lane_b(to_integer(b) + to_integer(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), 65521) == adler_spec_b(bytes, ((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)), to_integer(a), to_integer(b));
      invariant iter == chunks_exact::after(chunks_exact::chunks_exact(Slice<u8>::Slice(bytes, bytes.len() - bytes.len() % 4u64), 4u64), iterations);
      invariant ((adler_chunk_bytes(iter.len()) as uint32) as int32) % 4 == 0;
      invariant adler_chunk_bytes(iter.len()) <= bytes.len() - bytes.len() % 4u64;
      invariant adler_chunk_bytes(iter.len()) % 4u64 == 0u64;
      invariant to_integer(iter.len()) + iterations == to_integer((bytes.len() - bytes.len() % 4u64) / 4u64);
      invariant to_integer(a_vec.0[0]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(iter.len()) as uint32) as int32)));
      invariant to_integer(b_vec.0[0]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(iter.len()) as uint32) as int32)));
      invariant to_integer(a_vec.0[1]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(iter.len()) as uint32) as int32)));
      invariant to_integer(b_vec.0[1]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(iter.len()) as uint32) as int32)));
      invariant to_integer(a_vec.0[2]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(iter.len()) as uint32) as int32)));
      invariant to_integer(b_vec.0[2]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(iter.len()) as uint32) as int32)));
      invariant to_integer(a_vec.0[3]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(iter.len()) as uint32) as int32)));
      invariant to_integer(b_vec.0[3]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(iter.len()) as uint32) as int32)));
      maintain by {
       step(); step(); step(); step();
       if 0u64 < iter.len() {
       have chunks_exact::chunks_exact(Slice<u8>::Slice(bytes, bytes.len() - bytes.len() % 4u64), 4u64).len() == (bytes.len() - bytes.len() % 4u64) / 4u64 by {
        apply(chunks_exact::len_chunks_exact(Slice<u8>::Slice(bytes, bytes.len() - bytes.len() % 4u64), 4u64));
       }
       have 0 <= iterations;
       apply(adler_remainder_chunk_step(bytes.len() - bytes.len() % 4u64, iter.len(), iterations));
       have to_integer(((bytes.len() - bytes.len() % 4u64) / 4u64 - iter.len())) < to_integer(chunks_exact::chunks_exact(Slice<u8>::Slice(bytes, bytes.len() - bytes.len() % 4u64), 4u64).len()) by { rewrite(chunks_exact::chunks_exact(Slice<u8>::Slice(bytes, bytes.len() - bytes.len() % 4u64), 4u64).len(), (bytes.len() - bytes.len() % 4u64) / 4u64); close(); }
       have iter.nth(0u64) == chunks_exact::chunks_exact(Slice<u8>::Slice(bytes, bytes.len() - bytes.len() % 4u64), 4u64).nth(((bytes.len() - bytes.len() % 4u64) / 4u64 - iter.len())) by {
        apply(chunks_exact::nth_after(chunks_exact::chunks_exact(Slice<u8>::Slice(bytes, bytes.len() - bytes.len() % 4u64), 4u64), iterations, 0u64, ((bytes.len() - bytes.len() % 4u64) / 4u64 - iter.len())));
        close();
       }
       have iter.nth(0u64).len() == 4u64 by {
        apply(chunks_exact::nth_chunks_exact(Slice<u8>::Slice(bytes, bytes.len() - bytes.len() % 4u64), 4u64, ((bytes.len() - bytes.len() % 4u64) / 4u64 - iter.len())));
        close();
       }
       have iter.nth(0u64).as_ptr() == bytes + ((bytes.len() - bytes.len() % 4u64) / 4u64 - iter.len()) * 4u64 by {
        apply(chunks_exact::nth_chunks_exact(Slice<u8>::Slice(bytes, bytes.len() - bytes.len() % 4u64), 4u64, ((bytes.len() - bytes.len() % 4u64) / 4u64 - iter.len())));
        close();
       }
       have iter.after_next() == chunks_exact::after(chunks_exact::chunks_exact(Slice<u8>::Slice(bytes, bytes.len() - bytes.len() % 4u64), 4u64), iterations + 1) by {
        apply(chunks_exact::after_next_after(chunks_exact::chunks_exact(Slice<u8>::Slice(bytes, bytes.len() - bytes.len() % 4u64), 4u64), iterations));
        close();
       }
       have iter.after_next().len() == iter.len() - 1u64 by {
        apply(chunks_exact::len_after_next(iter));
       }
       apply(adler_chunk_bytes_step(iter.len()));
       apply(adler_chunk_bytes_position(bytes.len() - bytes.len() % 4u64, iter.len()));
       have iter.nth(0u64).as_ptr() == bytes + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len())) by {
        rewrite(iter.nth(0u64).as_ptr(), bytes + ((bytes.len() - bytes.len() % 4u64) / 4u64 - iter.len()) * 4u64);
        close();
       }
       have to_integer(bytes.len() - bytes.len() % 4u64) <= to_integer(bytes.len());
       have to_integer(((bytes.len() - bytes.len() % 4u64) / 4u64 - iter.len()) * 4u64) < to_integer(bytes.len()) by close() using { to_integer(((bytes.len() - bytes.len() % 4u64) / 4u64 - iter.len()) * 4u64) < to_integer(bytes.len() - bytes.len() % 4u64); to_integer(bytes.len() - bytes.len() % 4u64) <= to_integer(bytes.len()); };
       have to_integer(((bytes.len() - bytes.len() % 4u64) / 4u64 - iter.len()) * 4u64 + 3u64) < to_integer(bytes.len()) by close() using { to_integer(((bytes.len() - bytes.len() % 4u64) / 4u64 - iter.len()) * 4u64 + 3u64) < to_integer(bytes.len() - bytes.len() % 4u64); to_integer(bytes.len() - bytes.len() % 4u64) <= to_integer(bytes.len()); };
       have 4u64 <= adler_chunk_bytes(iter.len());
       have adler_chunk_bytes(iter.len()) <= 22208u64 by close() using { adler_chunk_bytes(iter.len()) <= bytes.len() - bytes.len() % 4u64; bytes.len() - bytes.len() % 4u64 <= 22204u64; };
       apply(adler_count_lane_step(adler_chunk_bytes(iter.len())));
       mark lane_head;
       have at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) % 4 == 0;
       have at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) <= old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32));
       have 4 <= at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32));
       have 0 <= at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32));
       have old((((bytes.len() - bytes.len() % 4u64) as u32) as i32)) <= 22208 by close() using { old((((bytes.len() - bytes.len() % 4u64) as u32) as i32)) <= 22204; };
       have 4u64 <= at(lane_head, adler_chunk_bytes(iter.len()));
       have at(lane_head, adler_chunk_bytes(iter.len())) <= bytes.len() - bytes.len() % 4u64;
       have bytes.len() - bytes.len() % 4u64 <= bytes.len();
       have (bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(iter.len())) <= bytes.len() by close() using { at(lane_head, adler_chunk_bytes(iter.len())) <= bytes.len() - bytes.len() % 4u64; bytes.len() - bytes.len() % 4u64 <= bytes.len(); };
       have 4u64 <= bytes.len() - ((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(iter.len()))) by close() using { 4u64 <= at(lane_head, adler_chunk_bytes(iter.len())); at(lane_head, adler_chunk_bytes(iter.len())) <= bytes.len() - bytes.len() % 4u64; bytes.len() - bytes.len() % 4u64 <= bytes.len(); };
       have 0 <= old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)) - at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) by close() using { 0 <= old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)); old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)) <= 22204; 0 <= at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) <= old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)); };
       have (old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)) - at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32))) + 4 <= old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)) by close() using { 0 <= old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)); old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)) <= 22204; 4 <= at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) <= old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)); };
       step_until(assignment(__rust_mir_69, 0).entry); step();
       step_until(assignment(__rust_mir_69_len, 0).entry); step();
       have __rust_mir_69_len == 4u64;
       have __rust_mir_69 == bytes + ((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(iter.len())));
       have iter == at(lane_head, iter.after_next());
       have iter.len() == at(lane_head, iter.len()) - 1u64;
       have 0u64 < at(lane_head, iter.len());
       have at(lane_head, iter.len()) <= 5551u64;
       have to_integer(iter.len()) == to_integer(at(lane_head, iter.len())) - 1;
       apply(adler_chunk_bytes_next(at(lane_head, iter.len()), iter.len()));
       have adler_chunk_bytes(iter.len()) == at(lane_head, adler_chunk_bytes(iter.len())) - 4u64;
       have at(lane_head, adler_chunk_bytes(iter.len())) <= 22208u64;
       have at(lane_head, adler_chunk_bytes(iter.len())) <= 2147483647u64 by close() using { at(lane_head, adler_chunk_bytes(iter.len())) <= 22208u64; };
       have adler_chunk_bytes(iter.len()) <= 2147483647u64 by close() using { adler_chunk_bytes(iter.len()) == at(lane_head, adler_chunk_bytes(iter.len())) - 4u64; at(lane_head, adler_chunk_bytes(iter.len())) <= 22208u64; };
       apply(adler_index_observation(at(lane_head, adler_chunk_bytes(iter.len()))));
       apply(adler_index_observation(adler_chunk_bytes(iter.len())));
       have ((adler_chunk_bytes(iter.len()) as uint32) as int32) == at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4 by close() using { to_integer(adler_chunk_bytes(iter.len()) as uint32 as int32) == to_integer(adler_chunk_bytes(iter.len())); to_integer(at(lane_head, adler_chunk_bytes(iter.len())) as uint32 as int32) == to_integer(at(lane_head, adler_chunk_bytes(iter.len()))); adler_chunk_bytes(iter.len()) == at(lane_head, adler_chunk_bytes(iter.len())) - 4u64; };
       apply(adler_signed_small_prefix(bytes.len()));
       apply(adler_small_signed_tail(bytes.len()));
       apply(adler_signed_partition_identity(bytes.len()));
       have (((bytes.len() - bytes.len() % 4u64) as u32) as i32) == old((((bytes.len() - bytes.len() % 4u64) as u32) as i32)) by close() using { bytes.len() == old(bytes.len()); };
       apply(adler_small_prefix_within_full(bytes.len()));
       have 0 <= ((bytes.len() as u32) as i32) by close();
       have ((bytes.len() as u32) as i32) <= 22207 by close();
       have old((((bytes.len() - bytes.len() % 4u64) as u32) as i32)) <= ((bytes.len() as u32) as i32) by close() using { (((bytes.len() - bytes.len() % 4u64) as u32) as i32) == old((((bytes.len() - bytes.len() % 4u64) as u32) as i32)); (((bytes.len() - bytes.len() % 4u64) as u32) as i32) <= ((bytes.len() as u32) as i32); };
       have adler_chunk_bytes(iter.len()) <= (bytes.len() - bytes.len() % 4u64) by close() using { adler_chunk_bytes(iter.len()) == at(lane_head, adler_chunk_bytes(iter.len())) - 4u64; 4u64 <= at(lane_head, adler_chunk_bytes(iter.len())); at(lane_head, adler_chunk_bytes(iter.len())) <= (bytes.len() - bytes.len() % 4u64); };
       have 4u64 <= (bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) by close() using { adler_chunk_bytes(iter.len()) == at(lane_head, adler_chunk_bytes(iter.len())) - 4u64; 4u64 <= at(lane_head, adler_chunk_bytes(iter.len())); at(lane_head, adler_chunk_bytes(iter.len())) <= (bytes.len() - bytes.len() % 4u64); };
       have (bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(iter.len())) == (bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64 by close() using { adler_chunk_bytes(iter.len()) == at(lane_head, adler_chunk_bytes(iter.len())) - 4u64; 4u64 <= at(lane_head, adler_chunk_bytes(iter.len())); at(lane_head, adler_chunk_bytes(iter.len())) <= (bytes.len() - bytes.len() % 4u64); };
       have __rust_mir_69 == bytes + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64) by { rewrite(__rust_mir_69, bytes + ((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(iter.len())))); rewrite((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(iter.len())), (bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64); normalize(); }
       have 0 <= ((adler_chunk_bytes(iter.len()) as uint32) as int32) by close() using { ((adler_chunk_bytes(iter.len()) as uint32) as int32) == at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4; 4 <= at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) <= old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)); old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)) <= 22204; };
       have ((adler_chunk_bytes(iter.len()) as uint32) as int32) <= (((bytes.len() - bytes.len() % 4u64) as uint32) as int32) by close() using { ((adler_chunk_bytes(iter.len()) as uint32) as int32) == at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4; 4 <= at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) <= old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)); old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)) <= 22204; (((bytes.len() - bytes.len() % 4u64) as uint32) as int32) == old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)); };
       have 4 <= (((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32) by close() using { ((adler_chunk_bytes(iter.len()) as uint32) as int32) == at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4; 4 <= at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) <= old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)); old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)) <= 22204; (((bytes.len() - bytes.len() % 4u64) as uint32) as int32) == old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)); };
       have (((bytes.len() - bytes.len() % 4u64) as u32) as i32) <= 22204 by normalize() using { (((bytes.len() - bytes.len() % 4u64) as u32) as i32) == old((((bytes.len() - bytes.len() % 4u64) as u32) as i32)); old((((bytes.len() - bytes.len() % 4u64) as u32) as i32)) <= 22204; };
       step_until(assignment(__rust_checked_23, 0).entry); step();
       mark from_call;
       have __rust_mir_69[0] == (bytes + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64))[0] by close() using { __rust_mir_69 == bytes + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64); };
       have __rust_mir_69[1] == (bytes + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64))[1] by close() using { __rust_mir_69 == bytes + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64); };
       have __rust_mir_69[2] == (bytes + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64))[2] by close() using { __rust_mir_69 == bytes + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64); };
       have __rust_mir_69[3] == (bytes + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64))[3] by close() using { __rust_mir_69 == bytes + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64); };
       step_until(assignment(__rust_mir_71, 0).entry);
       mark vector_a;
       have __rust_mir_68.0[0] == at(from_call, (__rust_mir_69[0] as u32)) by close();
       have __rust_mir_68.0[1] == at(from_call, (__rust_mir_69[1] as u32)) by close();
       have __rust_mir_68.0[2] == at(from_call, (__rust_mir_69[2] as u32)) by close();
       have __rust_mir_68.0[3] == at(from_call, (__rust_mir_69[3] as u32)) by close();
       have __rust_mir_69[0] == (bytes + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64))[0] by close() using { __rust_mir_69 == bytes + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64); };
       have __rust_mir_69[1] == (bytes + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64))[1] by close() using { __rust_mir_69 == bytes + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64); };
       have __rust_mir_69[2] == (bytes + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64))[2] by close() using { __rust_mir_69 == bytes + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64); };
       have __rust_mir_69[3] == (bytes + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64))[3] by close() using { __rust_mir_69 == bytes + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64); };
       have at(vector_a, __rust_mir_68.0[0]) == at(vector_a, (__rust_mir_69[0] as u32)) by close() using { __rust_mir_68.0[0] == at(from_call, (__rust_mir_69[0] as u32)); at(from_call, __rust_mir_69[0]) == (bytes + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64))[0]; __rust_mir_69[0] == (bytes + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64))[0]; };
       apply(adler_helper_byte_observation(at(vector_a, __rust_mir_69[0])));
       have to_integer(at(vector_a, __rust_mir_68.0[0])) == at(vector_a, to_integer((__rust_mir_69[0] as i32))) by {
        rewrite(at(vector_a, __rust_mir_68.0[0]), at(vector_a, (__rust_mir_69[0] as u32)));
        normalize() using { at(vector_a, to_integer((__rust_mir_69[0] as u32))) == at(vector_a, to_integer((__rust_mir_69[0] as i32))); };
       }
       have at(vector_a, __rust_mir_68.0[1]) == at(vector_a, (__rust_mir_69[1] as u32)) by close() using { __rust_mir_68.0[1] == at(from_call, (__rust_mir_69[1] as u32)); at(from_call, __rust_mir_69[1]) == (bytes + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64))[1]; __rust_mir_69[1] == (bytes + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64))[1]; };
       apply(adler_helper_byte_observation(at(vector_a, __rust_mir_69[1])));
       have to_integer(at(vector_a, __rust_mir_68.0[1])) == at(vector_a, to_integer((__rust_mir_69[1] as i32))) by {
        rewrite(at(vector_a, __rust_mir_68.0[1]), at(vector_a, (__rust_mir_69[1] as u32)));
        normalize() using { at(vector_a, to_integer((__rust_mir_69[1] as u32))) == at(vector_a, to_integer((__rust_mir_69[1] as i32))); };
       }
       have at(vector_a, __rust_mir_68.0[2]) == at(vector_a, (__rust_mir_69[2] as u32)) by close() using { __rust_mir_68.0[2] == at(from_call, (__rust_mir_69[2] as u32)); at(from_call, __rust_mir_69[2]) == (bytes + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64))[2]; __rust_mir_69[2] == (bytes + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64))[2]; };
       apply(adler_helper_byte_observation(at(vector_a, __rust_mir_69[2])));
       have to_integer(at(vector_a, __rust_mir_68.0[2])) == at(vector_a, to_integer((__rust_mir_69[2] as i32))) by {
        rewrite(at(vector_a, __rust_mir_68.0[2]), at(vector_a, (__rust_mir_69[2] as u32)));
        normalize() using { at(vector_a, to_integer((__rust_mir_69[2] as u32))) == at(vector_a, to_integer((__rust_mir_69[2] as i32))); };
       }
       have at(vector_a, __rust_mir_68.0[3]) == at(vector_a, (__rust_mir_69[3] as u32)) by close() using { __rust_mir_68.0[3] == at(from_call, (__rust_mir_69[3] as u32)); at(from_call, __rust_mir_69[3]) == (bytes + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64))[3]; __rust_mir_69[3] == (bytes + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64))[3]; };
       apply(adler_helper_byte_observation(at(vector_a, __rust_mir_69[3])));
       have to_integer(at(vector_a, __rust_mir_68.0[3])) == at(vector_a, to_integer((__rust_mir_69[3] as i32))) by {
        rewrite(at(vector_a, __rust_mir_68.0[3]), at(vector_a, (__rust_mir_69[3] as u32)));
        normalize() using { at(vector_a, to_integer((__rust_mir_69[3] as u32))) == at(vector_a, to_integer((__rust_mir_69[3] as i32))); };
       }
       have to_integer(bytes.len() - bytes.len() % 4u64) == to_integer(bytes.len()) - to_integer(bytes.len() % 4u64);
       have to_integer(adler_chunk_bytes(iter.len())) <= to_integer(bytes.len() - bytes.len() % 4u64) by close() using { adler_chunk_bytes(iter.len()) <= (bytes.len() - bytes.len() % 4u64); to_integer(bytes.len() - bytes.len() % 4u64) == to_integer(bytes.len()) - to_integer(bytes.len() % 4u64); };
       apply(integer::uint64_subtract_to_integer(bytes.len() - bytes.len() % 4u64, adler_chunk_bytes(iter.len())));
       have to_integer(4u64) <= to_integer((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len())) by close() using { 4u64 <= (bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()); to_integer(bytes.len() - bytes.len() % 4u64) == to_integer(bytes.len()) - to_integer(bytes.len() % 4u64); to_integer((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len())) == to_integer(bytes.len() - bytes.len() % 4u64) - to_integer(adler_chunk_bytes(iter.len())); };
       have to_integer(bytes.len() - bytes.len() % 4u64) <= to_integer(22204u64) by close() using { bytes.len() - bytes.len() % 4u64 <= 22204u64; to_integer(bytes.len() - bytes.len() % 4u64) == to_integer(bytes.len()) - to_integer(bytes.len() % 4u64); };
       apply(adler_count_previous_chunk_byte_observation(bytes, (bytes.len() - bytes.len() % 4u64), adler_chunk_bytes(iter.len()), 0));
       have at(vector_a, __rust_mir_69[0]) == (bytes + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64))[0] by close() using { __rust_mir_69 == bytes + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64); };
       have at(vector_a, to_integer((__rust_mir_69[0] as int32))) == to_integer(((bytes + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64))[0] as int32)) by { rewrite(at(vector_a, __rust_mir_69[0]), (bytes + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64))[0]); normalize(); }
       have to_integer(at(vector_a, __rust_mir_68.0[0])) == to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 0] as int32)) by close() using { to_integer(at(vector_a, __rust_mir_68.0[0])) == at(vector_a, to_integer((__rust_mir_69[0] as int32))); at(vector_a, to_integer((__rust_mir_69[0] as int32))) == to_integer(((bytes + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64))[0] as int32)); to_integer(((bytes + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64))[0] as int32)) == to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 0] as int32)); };
       apply(adler_count_previous_chunk_byte_observation(bytes, (bytes.len() - bytes.len() % 4u64), adler_chunk_bytes(iter.len()), 1));
       have at(vector_a, __rust_mir_69[1]) == (bytes + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64))[1] by close() using { __rust_mir_69 == bytes + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64); };
       have at(vector_a, to_integer((__rust_mir_69[1] as int32))) == to_integer(((bytes + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64))[1] as int32)) by { rewrite(at(vector_a, __rust_mir_69[1]), (bytes + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64))[1]); normalize(); }
       have to_integer(at(vector_a, __rust_mir_68.0[1])) == to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 1] as int32)) by close() using { to_integer(at(vector_a, __rust_mir_68.0[1])) == at(vector_a, to_integer((__rust_mir_69[1] as int32))); at(vector_a, to_integer((__rust_mir_69[1] as int32))) == to_integer(((bytes + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64))[1] as int32)); to_integer(((bytes + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64))[1] as int32)) == to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 1] as int32)); };
       apply(adler_count_previous_chunk_byte_observation(bytes, (bytes.len() - bytes.len() % 4u64), adler_chunk_bytes(iter.len()), 2));
       have at(vector_a, __rust_mir_69[2]) == (bytes + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64))[2] by close() using { __rust_mir_69 == bytes + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64); };
       have at(vector_a, to_integer((__rust_mir_69[2] as int32))) == to_integer(((bytes + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64))[2] as int32)) by { rewrite(at(vector_a, __rust_mir_69[2]), (bytes + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64))[2]); normalize(); }
       have to_integer(at(vector_a, __rust_mir_68.0[2])) == to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 2] as int32)) by close() using { to_integer(at(vector_a, __rust_mir_68.0[2])) == at(vector_a, to_integer((__rust_mir_69[2] as int32))); at(vector_a, to_integer((__rust_mir_69[2] as int32))) == to_integer(((bytes + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64))[2] as int32)); to_integer(((bytes + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64))[2] as int32)) == to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 2] as int32)); };
       apply(adler_count_previous_chunk_byte_observation(bytes, (bytes.len() - bytes.len() % 4u64), adler_chunk_bytes(iter.len()), 3));
       have at(vector_a, __rust_mir_69[3]) == (bytes + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64))[3] by close() using { __rust_mir_69 == bytes + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64); };
       have at(vector_a, to_integer((__rust_mir_69[3] as int32))) == to_integer(((bytes + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64))[3] as int32)) by { rewrite(at(vector_a, __rust_mir_69[3]), (bytes + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64))[3]); normalize(); }
       have to_integer(at(vector_a, __rust_mir_68.0[3])) == to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 3] as int32)) by close() using { to_integer(at(vector_a, __rust_mir_68.0[3])) == at(vector_a, to_integer((__rust_mir_69[3] as int32))); at(vector_a, to_integer((__rust_mir_69[3] as int32))) == to_integer(((bytes + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64))[3] as int32)); to_integer(((bytes + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64))[3] as int32)) == to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 3] as int32)); };
       have 0 <= to_integer((at(vector_a, a_vec.0[0])));
       have to_integer((at(vector_a, a_vec.0[0]))) <= 4294967295;
       have 0 <= to_integer((at(vector_a, b_vec.0[0])));
       have to_integer((at(vector_a, b_vec.0[0]))) <= 4294967295;
       have 0 <= to_integer((at(vector_a, __rust_mir_68.0[0])));
       have to_integer((at(vector_a, __rust_mir_68.0[0]))) <= 4294967295;
       have 0 <= to_integer(at(vector_a, a_vec.0[0]));
       have 0 <= to_integer(at(vector_a, b_vec.0[0]));
       have to_integer(at(vector_a, a_vec.0[0])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32))));
       have to_integer(at(vector_a, b_vec.0[0])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32))));
       have 0 <= to_integer(at(vector_a, __rust_mir_68.0[0]));
       have to_integer(at(vector_a, __rust_mir_68.0[0])) <= 255;
       apply(adler_lane_iterator_add_contracts(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)), at(vector_a, a_vec.0[0]), at(vector_a, b_vec.0[0]), at(vector_a, __rust_mir_68.0[0])));
       apply(adler_lane_iterator_native_preservation(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)), at(vector_a, a_vec.0[0]), at(vector_a, b_vec.0[0]), at(vector_a, __rust_mir_68.0[0])));
       have 0 <= to_integer((at(vector_a, a_vec.0[1])));
       have to_integer((at(vector_a, a_vec.0[1]))) <= 4294967295;
       have 0 <= to_integer((at(vector_a, b_vec.0[1])));
       have to_integer((at(vector_a, b_vec.0[1]))) <= 4294967295;
       have 0 <= to_integer((at(vector_a, __rust_mir_68.0[1])));
       have to_integer((at(vector_a, __rust_mir_68.0[1]))) <= 4294967295;
       have 0 <= to_integer(at(vector_a, a_vec.0[1]));
       have 0 <= to_integer(at(vector_a, b_vec.0[1]));
       have to_integer(at(vector_a, a_vec.0[1])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32))));
       have to_integer(at(vector_a, b_vec.0[1])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32))));
       have 0 <= to_integer(at(vector_a, __rust_mir_68.0[1]));
       have to_integer(at(vector_a, __rust_mir_68.0[1])) <= 255;
       apply(adler_lane_iterator_add_contracts(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)), at(vector_a, a_vec.0[1]), at(vector_a, b_vec.0[1]), at(vector_a, __rust_mir_68.0[1])));
       apply(adler_lane_iterator_native_preservation(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)), at(vector_a, a_vec.0[1]), at(vector_a, b_vec.0[1]), at(vector_a, __rust_mir_68.0[1])));
       have 0 <= to_integer((at(vector_a, a_vec.0[2])));
       have to_integer((at(vector_a, a_vec.0[2]))) <= 4294967295;
       have 0 <= to_integer((at(vector_a, b_vec.0[2])));
       have to_integer((at(vector_a, b_vec.0[2]))) <= 4294967295;
       have 0 <= to_integer((at(vector_a, __rust_mir_68.0[2])));
       have to_integer((at(vector_a, __rust_mir_68.0[2]))) <= 4294967295;
       have 0 <= to_integer(at(vector_a, a_vec.0[2]));
       have 0 <= to_integer(at(vector_a, b_vec.0[2]));
       have to_integer(at(vector_a, a_vec.0[2])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32))));
       have to_integer(at(vector_a, b_vec.0[2])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32))));
       have 0 <= to_integer(at(vector_a, __rust_mir_68.0[2]));
       have to_integer(at(vector_a, __rust_mir_68.0[2])) <= 255;
       apply(adler_lane_iterator_add_contracts(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)), at(vector_a, a_vec.0[2]), at(vector_a, b_vec.0[2]), at(vector_a, __rust_mir_68.0[2])));
       apply(adler_lane_iterator_native_preservation(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)), at(vector_a, a_vec.0[2]), at(vector_a, b_vec.0[2]), at(vector_a, __rust_mir_68.0[2])));
       have 0 <= to_integer((at(vector_a, a_vec.0[3])));
       have to_integer((at(vector_a, a_vec.0[3]))) <= 4294967295;
       have 0 <= to_integer((at(vector_a, b_vec.0[3])));
       have to_integer((at(vector_a, b_vec.0[3]))) <= 4294967295;
       have 0 <= to_integer((at(vector_a, __rust_mir_68.0[3])));
       have to_integer((at(vector_a, __rust_mir_68.0[3]))) <= 4294967295;
       have 0 <= to_integer(at(vector_a, a_vec.0[3]));
       have 0 <= to_integer(at(vector_a, b_vec.0[3]));
       have to_integer(at(vector_a, a_vec.0[3])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32))));
       have to_integer(at(vector_a, b_vec.0[3])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32))));
       have 0 <= to_integer(at(vector_a, __rust_mir_68.0[3]));
       have to_integer(at(vector_a, __rust_mir_68.0[3])) <= 255;
       apply(adler_lane_iterator_add_contracts(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)), at(vector_a, a_vec.0[3]), at(vector_a, b_vec.0[3]), at(vector_a, __rust_mir_68.0[3])));
       apply(adler_lane_iterator_native_preservation(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)), at(vector_a, a_vec.0[3]), at(vector_a, b_vec.0[3]), at(vector_a, __rust_mir_68.0[3])));
       step_until(assignment(__rust_mir_74, 0).entry);
       have a_vec.0[0] == at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0]);
       have b_vec.0[0] == at(vector_a, b_vec.0[0]);
       have to_integer(b_vec.0[0]) == to_integer(at(vector_a, b_vec.0[0])) by close() using { b_vec.0[0] == at(vector_a, b_vec.0[0]); };
       have to_integer(a_vec.0[0]) == to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0])) by close() using { a_vec.0[0] == at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0]); };
       have to_integer(b_vec.0[0]) + to_integer(a_vec.0[0]) <= 4294967295 by close() using { to_integer(b_vec.0[0]) == to_integer(at(vector_a, b_vec.0[0])); to_integer(a_vec.0[0]) == to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0])); to_integer(at(vector_a, b_vec.0[0])) + to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0])) <= 4294967295; };
       have a_vec.0[1] == at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1]);
       have b_vec.0[1] == at(vector_a, b_vec.0[1]);
       have to_integer(b_vec.0[1]) == to_integer(at(vector_a, b_vec.0[1])) by close() using { b_vec.0[1] == at(vector_a, b_vec.0[1]); };
       have to_integer(a_vec.0[1]) == to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1])) by close() using { a_vec.0[1] == at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1]); };
       have to_integer(b_vec.0[1]) + to_integer(a_vec.0[1]) <= 4294967295 by close() using { to_integer(b_vec.0[1]) == to_integer(at(vector_a, b_vec.0[1])); to_integer(a_vec.0[1]) == to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1])); to_integer(at(vector_a, b_vec.0[1])) + to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1])) <= 4294967295; };
       have a_vec.0[2] == at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2]);
       have b_vec.0[2] == at(vector_a, b_vec.0[2]);
       have to_integer(b_vec.0[2]) == to_integer(at(vector_a, b_vec.0[2])) by close() using { b_vec.0[2] == at(vector_a, b_vec.0[2]); };
       have to_integer(a_vec.0[2]) == to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2])) by close() using { a_vec.0[2] == at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2]); };
       have to_integer(b_vec.0[2]) + to_integer(a_vec.0[2]) <= 4294967295 by close() using { to_integer(b_vec.0[2]) == to_integer(at(vector_a, b_vec.0[2])); to_integer(a_vec.0[2]) == to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2])); to_integer(at(vector_a, b_vec.0[2])) + to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2])) <= 4294967295; };
       have a_vec.0[3] == at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3]);
       have b_vec.0[3] == at(vector_a, b_vec.0[3]);
       have to_integer(b_vec.0[3]) == to_integer(at(vector_a, b_vec.0[3])) by close() using { b_vec.0[3] == at(vector_a, b_vec.0[3]); };
       have to_integer(a_vec.0[3]) == to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3])) by close() using { a_vec.0[3] == at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3]); };
       have to_integer(b_vec.0[3]) + to_integer(a_vec.0[3]) <= 4294967295 by close() using { to_integer(b_vec.0[3]) == to_integer(at(vector_a, b_vec.0[3])); to_integer(a_vec.0[3]) == to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3])); to_integer(at(vector_a, b_vec.0[3])) + to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3])) <= 4294967295; };
       mark vector_b;
       step_until(loop.back_edge);
       have a_vec.0[0] == at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0]);
       have b_vec.0[0] == at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0]));
       have to_integer(a_vec.0[0]) == to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0])) by close() using { a_vec.0[0] == at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0]); };
       have adler_lane_a_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(iter.len()) as uint32) as int32))) == adler_lane_a_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)) by close() using { ((adler_chunk_bytes(iter.len()) as uint32) as int32) == at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4; };
       have to_integer(a_vec.0[0]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(iter.len()) as uint32) as int32))) by close() using { to_integer(a_vec.0[0]) == to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0])); adler_lane_a_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(iter.len()) as uint32) as int32))) == adler_lane_a_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)); to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)); };
       have to_integer(b_vec.0[0]) == to_integer(at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0]))) by close() using { b_vec.0[0] == at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0])); };
       have adler_lane_b_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(iter.len()) as uint32) as int32))) == adler_lane_b_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)) by close() using { ((adler_chunk_bytes(iter.len()) as uint32) as int32) == at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4; };
       have to_integer(b_vec.0[0]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(iter.len()) as uint32) as int32))) by close() using { to_integer(b_vec.0[0]) == to_integer(at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0]))); adler_lane_b_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(iter.len()) as uint32) as int32))) == adler_lane_b_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)); to_integer(at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0]))) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)); };
       have a_vec.0[1] == at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1]);
       have b_vec.0[1] == at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1]));
       have to_integer(a_vec.0[1]) == to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1])) by close() using { a_vec.0[1] == at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1]); };
       have adler_lane_a_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(iter.len()) as uint32) as int32))) == adler_lane_a_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)) by close() using { ((adler_chunk_bytes(iter.len()) as uint32) as int32) == at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4; };
       have to_integer(a_vec.0[1]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(iter.len()) as uint32) as int32))) by close() using { to_integer(a_vec.0[1]) == to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1])); adler_lane_a_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(iter.len()) as uint32) as int32))) == adler_lane_a_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)); to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)); };
       have to_integer(b_vec.0[1]) == to_integer(at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1]))) by close() using { b_vec.0[1] == at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1])); };
       have adler_lane_b_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(iter.len()) as uint32) as int32))) == adler_lane_b_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)) by close() using { ((adler_chunk_bytes(iter.len()) as uint32) as int32) == at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4; };
       have to_integer(b_vec.0[1]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(iter.len()) as uint32) as int32))) by close() using { to_integer(b_vec.0[1]) == to_integer(at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1]))); adler_lane_b_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(iter.len()) as uint32) as int32))) == adler_lane_b_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)); to_integer(at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1]))) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)); };
       have a_vec.0[2] == at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2]);
       have b_vec.0[2] == at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2]));
       have to_integer(a_vec.0[2]) == to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2])) by close() using { a_vec.0[2] == at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2]); };
       have adler_lane_a_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(iter.len()) as uint32) as int32))) == adler_lane_a_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)) by close() using { ((adler_chunk_bytes(iter.len()) as uint32) as int32) == at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4; };
       have to_integer(a_vec.0[2]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(iter.len()) as uint32) as int32))) by close() using { to_integer(a_vec.0[2]) == to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2])); adler_lane_a_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(iter.len()) as uint32) as int32))) == adler_lane_a_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)); to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)); };
       have to_integer(b_vec.0[2]) == to_integer(at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2]))) by close() using { b_vec.0[2] == at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2])); };
       have adler_lane_b_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(iter.len()) as uint32) as int32))) == adler_lane_b_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)) by close() using { ((adler_chunk_bytes(iter.len()) as uint32) as int32) == at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4; };
       have to_integer(b_vec.0[2]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(iter.len()) as uint32) as int32))) by close() using { to_integer(b_vec.0[2]) == to_integer(at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2]))); adler_lane_b_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(iter.len()) as uint32) as int32))) == adler_lane_b_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)); to_integer(at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2]))) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)); };
       have a_vec.0[3] == at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3]);
       have b_vec.0[3] == at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3]));
       have to_integer(a_vec.0[3]) == to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3])) by close() using { a_vec.0[3] == at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3]); };
       have adler_lane_a_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(iter.len()) as uint32) as int32))) == adler_lane_a_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)) by close() using { ((adler_chunk_bytes(iter.len()) as uint32) as int32) == at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4; };
       have to_integer(a_vec.0[3]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(iter.len()) as uint32) as int32))) by close() using { to_integer(a_vec.0[3]) == to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3])); adler_lane_a_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(iter.len()) as uint32) as int32))) == adler_lane_a_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)); to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)); };
       have to_integer(b_vec.0[3]) == to_integer(at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3]))) by close() using { b_vec.0[3] == at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3])); };
       have adler_lane_b_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(iter.len()) as uint32) as int32))) == adler_lane_b_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)) by close() using { ((adler_chunk_bytes(iter.len()) as uint32) as int32) == at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4; };
       have to_integer(b_vec.0[3]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(iter.len()) as uint32) as int32))) by close() using { to_integer(b_vec.0[3]) == to_integer(at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3]))); adler_lane_b_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(iter.len()) as uint32) as int32))) == adler_lane_b_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)); to_integer(at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3]))) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)); };
       have 0 <= ((adler_chunk_bytes(iter.len()) as uint32) as int32) by close() using { ((adler_chunk_bytes(iter.len()) as uint32) as int32) == at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4; 4 <= at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)); };
       have ((adler_chunk_bytes(iter.len()) as uint32) as int32) <= old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)) by close() using { ((adler_chunk_bytes(iter.len()) as uint32) as int32) == at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4; 4 <= at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) <= old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)); old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)) <= 22204; };
       have 0 <= ((adler_chunk_bytes(iter.len()) as uint32) as int32) and ((adler_chunk_bytes(iter.len()) as uint32) as int32) <= old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)) by close();
       have ((adler_chunk_bytes(iter.len()) as uint32) as int32) % 4 == 0 by { rewrite(((adler_chunk_bytes(iter.len()) as uint32) as int32), at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4); normalize() using { at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) % 4 == 0; 4 <= at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) <= old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)); old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)) <= 22204; }; }
       have adler_chunk_bytes(iter.len()) <= bytes.len() - bytes.len() % 4u64 by close() using { adler_chunk_bytes(iter.len()) == at(lane_head, adler_chunk_bytes(iter.len())) - 4u64; 4u64 <= at(lane_head, adler_chunk_bytes(iter.len())); at(lane_head, adler_chunk_bytes(iter.len())) <= bytes.len() - bytes.len() % 4u64; bytes.len() % 4u64 <= bytes.len(); };
       have (bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(iter.len())) <= 18446744073709551611u64 by close() using { 4u64 <= at(lane_head, adler_chunk_bytes(iter.len())); at(lane_head, adler_chunk_bytes(iter.len())) <= bytes.len() - bytes.len() % 4u64; bytes.len() % 4u64 <= bytes.len(); };
       have (bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) == ((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(iter.len()))) + 4u64 by close() using { adler_chunk_bytes(iter.len()) == at(lane_head, adler_chunk_bytes(iter.len())) - 4u64; 4u64 <= at(lane_head, adler_chunk_bytes(iter.len())); at(lane_head, adler_chunk_bytes(iter.len())) <= bytes.len() - bytes.len() % 4u64; bytes.len() % 4u64 <= bytes.len(); };
       have (at(lane_head, adler_chunk_bytes(iter.len())) - 4u64) % 4u64 == at(lane_head, adler_chunk_bytes(iter.len()) % 4u64) by normalize() using { 4u64 <= at(lane_head, adler_chunk_bytes(iter.len())); };
       have adler_chunk_bytes(iter.len()) % 4u64 == 0u64 by { rewrite(adler_chunk_bytes(iter.len()), at(lane_head, adler_chunk_bytes(iter.len())) - 4u64); rewrite((at(lane_head, adler_chunk_bytes(iter.len())) - 4u64) % 4u64, at(lane_head, adler_chunk_bytes(iter.len()) % 4u64)); close(); }
       have adler_chunk_bytes(iter.len()) < at(lane_head, adler_chunk_bytes(iter.len())) by close() using { adler_chunk_bytes(iter.len()) == at(lane_head, adler_chunk_bytes(iter.len())) - 4u64; 4u64 <= at(lane_head, adler_chunk_bytes(iter.len())); };
       have ((adler_chunk_bytes(iter.len()) as uint32) as int32) < at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) by close() using { ((adler_chunk_bytes(iter.len()) as uint32) as int32) == at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4; 4 <= at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) <= old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)); old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)) <= 22204; };
       have (((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) == (((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) by close() using { ((adler_chunk_bytes(iter.len()) as uint32) as int32) == at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4; 4 <= at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) <= old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)); old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)) <= 22204; (((bytes.len() - bytes.len() % 4u64) as uint32) as int32) == old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)); };
       have 0 <= (((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) by close() using { (((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) == (((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)); 4 <= at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) <= old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)); old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)) <= 22204; (((bytes.len() - bytes.len() % 4u64) as uint32) as int32) == old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)); };
       have (((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) <= 2147483643 by close() using { (((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) == (((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)); 4 <= at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) <= old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)); old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)) <= 22204; (((bytes.len() - bytes.len() % 4u64) as uint32) as int32) == old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)); };
       have truncating_remainder(adler_lane_a(to_integer(a), to_integer(at(vector_a, a_vec.0[0])), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3]))), 65521) == adler_spec_a(bytes, (((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4), to_integer(a)) by { rewrite((((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4), (((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32))); close(); }
       have 0 <= to_integer(at(vector_a, a_vec.0[0])) by close();
       have 0 <= to_integer(at(vector_a, a_vec.0[1])) by close();
       have 0 <= to_integer(at(vector_a, a_vec.0[2])) by close();
       have 0 <= to_integer(at(vector_a, a_vec.0[3])) by close();
       have 0 <= adler_lane_a(to_integer(a), to_integer(at(vector_a, a_vec.0[0])), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3]))) by {
        unfold(adler_lane_a(to_integer(a), to_integer(at(vector_a, a_vec.0[0])), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3]))));
        close() using { 0 <= to_integer(a); 0 <= to_integer(at(vector_a, a_vec.0[0])); 0 <= to_integer(at(vector_a, a_vec.0[1])); 0 <= to_integer(at(vector_a, a_vec.0[2])); 0 <= to_integer(at(vector_a, a_vec.0[3])); };
       }
       have defined(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32))) by close();
       have to_integer(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32))) == to_integer((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)) - to_integer(((adler_chunk_bytes(iter.len()) as uint32) as int32)) by close();
       have defined((((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)) by close();
       have 0 <= to_integer((((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)) by close();
       have to_integer((((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)) == to_integer(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32))) - 4 by close();
       have to_integer((((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)) <= 2147483643 by close() using { to_integer((((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)) == to_integer(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32))) - 4; to_integer(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32))) == to_integer((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)) - to_integer(((adler_chunk_bytes(iter.len()) as uint32) as int32)); (((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) <= 2147483643; };
       apply(adler_prefix_a_step_four(bytes, (((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4), to_integer(a), adler_lane_a(to_integer(a), to_integer(at(vector_a, a_vec.0[0])), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3])))));
       apply(integer::uint32_add_to_integer(at(vector_a, a_vec.0[0]), at(vector_a, __rust_mir_68.0[0])));
       apply(integer::uint32_add_to_integer(at(vector_a, a_vec.0[1]), at(vector_a, __rust_mir_68.0[1])));
       apply(integer::uint32_add_to_integer(at(vector_a, a_vec.0[2]), at(vector_a, __rust_mir_68.0[2])));
       apply(integer::uint32_add_to_integer(at(vector_a, a_vec.0[3]), at(vector_a, __rust_mir_68.0[3])));
       have defined((((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 0) by close();
       have to_integer((((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 0) == to_integer((((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)) by close();
       have to_integer(at(vector_a, __rust_mir_68.0[0])) == to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)] as int32)) by { rewrite(to_integer(at(vector_a, __rust_mir_68.0[0])), to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 0] as int32))); close(); }
       have adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])) == adler_lane_a(to_integer(a), to_integer(at(vector_a, a_vec.0[0])), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3]))) + (to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)] as int32)) + to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 1] as int32)) + to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 2] as int32)) + to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 3] as int32))) by { unfold(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]))); unfold(adler_lane_a(to_integer(a), to_integer(at(vector_a, a_vec.0[0])), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3])))); close() using { to_integer(a_vec.0[0]) == to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0])); to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0])) == to_integer(at(vector_a, a_vec.0[0])) + to_integer(at(vector_a, __rust_mir_68.0[0])); to_integer(at(vector_a, __rust_mir_68.0[0])) == to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)] as int32)); to_integer(a_vec.0[1]) == to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1])); to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1])) == to_integer(at(vector_a, a_vec.0[1])) + to_integer(at(vector_a, __rust_mir_68.0[1])); to_integer(at(vector_a, __rust_mir_68.0[1])) == to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 1] as int32)); to_integer(a_vec.0[2]) == to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2])); to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2])) == to_integer(at(vector_a, a_vec.0[2])) + to_integer(at(vector_a, __rust_mir_68.0[2])); to_integer(at(vector_a, __rust_mir_68.0[2])) == to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 2] as int32)); to_integer(a_vec.0[3]) == to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3])); to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3])) == to_integer(at(vector_a, a_vec.0[3])) + to_integer(at(vector_a, __rust_mir_68.0[3])); to_integer(at(vector_a, __rust_mir_68.0[3])) == to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 3] as int32)); }; }
       have ((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) == (((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 4 by close() using { ((adler_chunk_bytes(iter.len()) as uint32) as int32) == at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4; 4 <= at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) <= old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)); old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)) <= 22204; (((bytes.len() - bytes.len() % 4u64) as uint32) as int32) == old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)); };
       have truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521) == adler_spec_a(bytes, ((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)), to_integer(a)) by { rewrite(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), adler_lane_a(to_integer(a), to_integer(at(vector_a, a_vec.0[0])), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3]))) + (to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)] as int32)) + to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 1] as int32)) + to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 2] as int32)) + to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 3] as int32)))); rewrite(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)), (((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 4); close(); }
       have 0 <= to_integer(b);
       have to_integer(b) <= 4294967295;
       have to_integer(a) <= to_integer(65520u32);
       have to_integer((((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)) == to_integer((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32))) by close() using { (((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) == (((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)); };
       have 0 <= adler_lane_b(to_integer(b) + to_integer((((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)) * to_integer(a), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3])), to_integer(at(vector_a, b_vec.0[0])), to_integer(at(vector_a, b_vec.0[1])), to_integer(at(vector_a, b_vec.0[2])), to_integer(at(vector_a, b_vec.0[3]))) by { rewrite(to_integer((((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)), to_integer((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)))); close(); }
       have truncating_remainder(adler_lane_b(to_integer(b) + to_integer((((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)) * to_integer(a), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3])), to_integer(at(vector_a, b_vec.0[0])), to_integer(at(vector_a, b_vec.0[1])), to_integer(at(vector_a, b_vec.0[2])), to_integer(at(vector_a, b_vec.0[3]))), 65521) == adler_spec_b(bytes, (((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4), to_integer(a), to_integer(b)) by { rewrite(to_integer((((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)), to_integer((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)))); rewrite((((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4), (((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32))); close(); }
       apply(adler_prefix_b_step_four(bytes, (((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4), to_integer(a), to_integer(b), adler_lane_a(to_integer(a), to_integer(at(vector_a, a_vec.0[0])), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3]))), adler_lane_b(to_integer(b) + to_integer((((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)) * to_integer(a), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3])), to_integer(at(vector_a, b_vec.0[0])), to_integer(at(vector_a, b_vec.0[1])), to_integer(at(vector_a, b_vec.0[2])), to_integer(at(vector_a, b_vec.0[3])))));
       have (((bytes.len() - bytes.len() % 4u64) as u32) as i32) <= 22204 by close() using { (((bytes.len() - bytes.len() % 4u64) as u32) as i32) == old((((bytes.len() - bytes.len() % 4u64) as u32) as i32)); old((((bytes.len() - bytes.len() % 4u64) as u32) as i32)) <= 22204; };
       have 4 <= ((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) by close() using { ((adler_chunk_bytes(iter.len()) as uint32) as int32) == at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4; 4 <= at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) <= old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)); old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)) <= 22204; (((bytes.len() - bytes.len() % 4u64) as uint32) as int32) == old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)); };
       have 4 <= to_integer((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) by close() using { to_integer((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) == to_integer((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)) - to_integer(((adler_chunk_bytes(iter.len()) as uint32) as int32)); 4 <= ((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)); };
       apply(adler_small_prefix_integer_advance((((bytes.len() - bytes.len() % 4u64) as uint32) as int32), ((adler_chunk_bytes(iter.len()) as uint32) as int32)));
       have to_integer(b) + to_integer(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32))) * to_integer(a) == (to_integer(b) + to_integer((((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)) * to_integer(a)) + 4 * to_integer(a) by { rewrite(to_integer(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32))), to_integer((((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)) + 4); close() using {  }; }
       apply(integer::uint32_add_to_integer(at(vector_a, b_vec.0[0]), at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0])));
       apply(integer::uint32_add_to_integer(at(vector_a, b_vec.0[1]), at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1])));
       apply(integer::uint32_add_to_integer(at(vector_a, b_vec.0[2]), at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2])));
       apply(integer::uint32_add_to_integer(at(vector_a, b_vec.0[3]), at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3])));
       have adler_lane_b(to_integer(b) + to_integer(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])) == (adler_lane_b(to_integer(b) + to_integer((((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)) * to_integer(a), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3])), to_integer(at(vector_a, b_vec.0[0])), to_integer(at(vector_a, b_vec.0[1])), to_integer(at(vector_a, b_vec.0[2])), to_integer(at(vector_a, b_vec.0[3]))) + 4 * adler_lane_a(to_integer(a), to_integer(at(vector_a, a_vec.0[0])), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3]))) + (4 * to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)] as int32)) + 3 * to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 1] as int32)) + 2 * to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 2] as int32)) + to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 3] as int32)))) by { unfold(adler_lane_b(to_integer(b) + to_integer(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3]))); unfold(adler_lane_b(to_integer(b) + to_integer((((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)) * to_integer(a), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3])), to_integer(at(vector_a, b_vec.0[0])), to_integer(at(vector_a, b_vec.0[1])), to_integer(at(vector_a, b_vec.0[2])), to_integer(at(vector_a, b_vec.0[3])))); unfold(adler_lane_a(to_integer(a), to_integer(at(vector_a, a_vec.0[0])), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3])))); close() using { to_integer(b) + to_integer(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32))) * to_integer(a) == (to_integer(b) + to_integer((((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)) * to_integer(a)) + 4 * to_integer(a); to_integer(a_vec.0[0]) == to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0])); to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0])) == to_integer(at(vector_a, a_vec.0[0])) + to_integer(at(vector_a, __rust_mir_68.0[0])); to_integer(b_vec.0[0]) == to_integer(at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0]))); to_integer(at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0]))) == to_integer(at(vector_a, b_vec.0[0])) + to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0])); to_integer(at(vector_a, __rust_mir_68.0[0])) == to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)] as int32)); to_integer(a_vec.0[1]) == to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1])); to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1])) == to_integer(at(vector_a, a_vec.0[1])) + to_integer(at(vector_a, __rust_mir_68.0[1])); to_integer(b_vec.0[1]) == to_integer(at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1]))); to_integer(at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1]))) == to_integer(at(vector_a, b_vec.0[1])) + to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1])); to_integer(at(vector_a, __rust_mir_68.0[1])) == to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 1] as int32)); to_integer(a_vec.0[2]) == to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2])); to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2])) == to_integer(at(vector_a, a_vec.0[2])) + to_integer(at(vector_a, __rust_mir_68.0[2])); to_integer(b_vec.0[2]) == to_integer(at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2]))); to_integer(at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2]))) == to_integer(at(vector_a, b_vec.0[2])) + to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2])); to_integer(at(vector_a, __rust_mir_68.0[2])) == to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 2] as int32)); to_integer(a_vec.0[3]) == to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3])); to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3])) == to_integer(at(vector_a, a_vec.0[3])) + to_integer(at(vector_a, __rust_mir_68.0[3])); to_integer(b_vec.0[3]) == to_integer(at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3]))); to_integer(at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3]))) == to_integer(at(vector_a, b_vec.0[3])) + to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3])); to_integer(at(vector_a, __rust_mir_68.0[3])) == to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 3] as int32)); }; }
       have truncating_remainder(adler_lane_b(to_integer(b) + to_integer(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), 65521) == adler_spec_b(bytes, ((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)), to_integer(a), to_integer(b)) by { rewrite(adler_lane_b(to_integer(b) + to_integer(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), (adler_lane_b(to_integer(b) + to_integer((((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)) * to_integer(a), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3])), to_integer(at(vector_a, b_vec.0[0])), to_integer(at(vector_a, b_vec.0[1])), to_integer(at(vector_a, b_vec.0[2])), to_integer(at(vector_a, b_vec.0[3]))) + 4 * adler_lane_a(to_integer(a), to_integer(at(vector_a, a_vec.0[0])), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3]))) + (4 * to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)] as int32)) + 3 * to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 1] as int32)) + 2 * to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 2] as int32)) + to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 3] as int32))))); rewrite(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)), (((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 4); close(); }
       apply(adler_byte_bounds(bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)]));
       apply(adler_byte_bounds(bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 1]));
       apply(adler_byte_bounds(bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 2]));
       apply(adler_byte_bounds(bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 3]));
       have 0 <= adler_lane_b(to_integer(b) + to_integer((((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)) * to_integer(a), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3])), to_integer(at(vector_a, b_vec.0[0])), to_integer(at(vector_a, b_vec.0[1])), to_integer(at(vector_a, b_vec.0[2])), to_integer(at(vector_a, b_vec.0[3]))) + 4 * adler_lane_a(to_integer(a), to_integer(at(vector_a, a_vec.0[0])), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3]))) by close() using { 0 <= adler_lane_b(to_integer(b) + to_integer((((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)) * to_integer(a), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3])), to_integer(at(vector_a, b_vec.0[0])), to_integer(at(vector_a, b_vec.0[1])), to_integer(at(vector_a, b_vec.0[2])), to_integer(at(vector_a, b_vec.0[3]))); 0 <= adler_lane_a(to_integer(a), to_integer(at(vector_a, a_vec.0[0])), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3]))); };
       have 0 <= (4 * to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)] as int32))) by close() using { 0 <= to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)] as int32)); };
       have 0 <= (4 * to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)] as int32)) + 3 * to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 1] as int32))) by close() using { 0 <= to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)] as int32)); 0 <= to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 1] as int32)); };
       have 0 <= (4 * to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)] as int32)) + 3 * to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 1] as int32)) + 2 * to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 2] as int32))) by close() using { 0 <= (4 * to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)] as int32)) + 3 * to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 1] as int32))); 0 <= to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 2] as int32)); };
       have 0 <= (4 * to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)] as int32)) + 3 * to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 1] as int32)) + 2 * to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 2] as int32)) + to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 3] as int32))) by close() using { 0 <= (4 * to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)] as int32)) + 3 * to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 1] as int32)) + 2 * to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 2] as int32))); 0 <= to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 3] as int32)); };
       have 0 <= adler_lane_b(to_integer(b) + to_integer(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])) by { rewrite(adler_lane_b(to_integer(b) + to_integer(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), (adler_lane_b(to_integer(b) + to_integer((((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)) * to_integer(a), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3])), to_integer(at(vector_a, b_vec.0[0])), to_integer(at(vector_a, b_vec.0[1])), to_integer(at(vector_a, b_vec.0[2])), to_integer(at(vector_a, b_vec.0[3]))) + 4 * adler_lane_a(to_integer(a), to_integer(at(vector_a, a_vec.0[0])), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3]))) + (4 * to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)] as int32)) + 3 * to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 1] as int32)) + 2 * to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 2] as int32)) + to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 3] as int32))))); close() using { 0 <= adler_lane_b(to_integer(b) + to_integer((((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)) * to_integer(a), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3])), to_integer(at(vector_a, b_vec.0[0])), to_integer(at(vector_a, b_vec.0[1])), to_integer(at(vector_a, b_vec.0[2])), to_integer(at(vector_a, b_vec.0[3]))) + 4 * adler_lane_a(to_integer(a), to_integer(at(vector_a, a_vec.0[0])), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3]))); 0 <= (4 * to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)] as int32)) + 3 * to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 1] as int32)) + 2 * to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 2] as int32)) + to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 3] as int32))); }; }
       have defined(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)) - (((adler_chunk_bytes(iter.len()) as uint32) as int32)));
       have iter == at(lane_head, iter.after_next());
       have iter.len() == at(lane_head, iter.len()) - 1u64;
       have 0u64 < at(lane_head, iter.len());
       have iter.len() < at(lane_head, iter.len());
       have iter == chunks_exact::after(chunks_exact::chunks_exact(Slice<u8>::Slice(bytes, bytes.len() - bytes.len() % 4u64), 4u64), iterations + 1) by close() using { iter == at(lane_head, iter.after_next()); at(lane_head, iter.after_next()) == chunks_exact::after(chunks_exact::chunks_exact(Slice<u8>::Slice(bytes, bytes.len() - bytes.len() % 4u64), 4u64), iterations + 1); };
       have to_integer(iter.len()) + (iterations + 1) == to_integer((bytes.len() - bytes.len() % 4u64) / 4u64) by close() using { to_integer(iter.len()) == to_integer(at(lane_head, iter.len())) - 1; at(lane_head, to_integer(iter.len())) + iterations == to_integer((bytes.len() - bytes.len() % 4u64) / 4u64); };
       } else {
        step();
       }
      }
     }
     have loop(2).iter.len() == 0u64;
     have adler_chunk_bytes(loop(2).iter.len()) == 0u64 by { rewrite(loop(2).iter.len(), 0u64); apply(adler_chunk_bytes_zero()); close(); }
     have ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32) == 0 by { rewrite(adler_chunk_bytes(loop(2).iter.len()), 0u64); normalize(); }
     have truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521) == adler_spec_a(bytes, (((bytes.len() - bytes.len() % 4u64) as u32) as i32), to_integer(a)) by {
      have (((bytes.len() - bytes.len() % 4u64) as uint32) as int32) == (((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32) by { rewrite(((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32), 0); normalize(); }
      rewrite((((bytes.len() - bytes.len() % 4u64) as uint32) as int32), (((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32));
      close();
     }
     have truncating_remainder(adler_lane_b(to_integer(b) + to_integer((((bytes.len() - bytes.len() % 4u64) as u32) as i32)) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), 65521) == adler_spec_b(bytes, (((bytes.len() - bytes.len() % 4u64) as u32) as i32), to_integer(a), to_integer(b)) by {
      have (((bytes.len() - bytes.len() % 4u64) as uint32) as int32) == (((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32) by { rewrite(((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32), 0); normalize(); }
      have to_integer((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)) == to_integer(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32))) by close() using { (((bytes.len() - bytes.len() % 4u64) as uint32) as int32) == (((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32); };
      have adler_lane_b(to_integer(b) + to_integer((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])) == adler_lane_b(to_integer(b) + to_integer(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])) by { rewrite(to_integer((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), to_integer(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32)))); close(); }
      have adler_spec_b(bytes, (((bytes.len() - bytes.len() % 4u64) as uint32) as int32), to_integer(a), to_integer(b)) == adler_spec_b(bytes, ((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32)), to_integer(a), to_integer(b)) by close() using { (((bytes.len() - bytes.len() % 4u64) as uint32) as int32) == (((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32); };
      rewrite(adler_lane_b(to_integer(b) + to_integer((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), adler_lane_b(to_integer(b) + to_integer(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])));
      rewrite(adler_spec_b(bytes, (((bytes.len() - bytes.len() % 4u64) as uint32) as int32), to_integer(a), to_integer(b)), adler_spec_b(bytes, ((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32)), to_integer(a), to_integer(b)));
      close();
     }
     have 0 <= adler_lane_b(to_integer(b) + to_integer((((bytes.len() - bytes.len() % 4u64) as u32) as i32)) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])) by {
      have (((bytes.len() - bytes.len() % 4u64) as uint32) as int32) == ((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32)) by { rewrite(((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32), 0); normalize(); }
      have to_integer((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)) == to_integer(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32))) by close() using { (((bytes.len() - bytes.len() % 4u64) as uint32) as int32) == ((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32)); };
      rewrite(to_integer((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), to_integer(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32)))); close();
     }
     mark vector_prefix;
     have truncating_remainder(adler_lane_b(to_integer(at(vector_prefix, b)) + to_integer((((bytes.len() - bytes.len() % 4u64) as u32) as i32)) * to_integer(at(vector_prefix, a)), to_integer(at(vector_prefix, a_vec.0[1])), to_integer(at(vector_prefix, a_vec.0[2])), to_integer(at(vector_prefix, a_vec.0[3])), to_integer(at(vector_prefix, b_vec.0[0])), to_integer(at(vector_prefix, b_vec.0[1])), to_integer(at(vector_prefix, b_vec.0[2])), to_integer(at(vector_prefix, b_vec.0[3]))), 65521) == adler_spec_b(bytes, (((bytes.len() - bytes.len() % 4u64) as u32) as i32), to_integer(at(vector_prefix, a)), to_integer(at(vector_prefix, b)));
     have 0 <= adler_lane_b(to_integer(at(vector_prefix, b)) + to_integer((((bytes.len() - bytes.len() % 4u64) as u32) as i32)) * to_integer(at(vector_prefix, a)), to_integer(at(vector_prefix, a_vec.0[1])), to_integer(at(vector_prefix, a_vec.0[2])), to_integer(at(vector_prefix, a_vec.0[3])), to_integer(at(vector_prefix, b_vec.0[0])), to_integer(at(vector_prefix, b_vec.0[1])), to_integer(at(vector_prefix, b_vec.0[2])), to_integer(at(vector_prefix, b_vec.0[3])));
     have truncating_remainder(adler_lane_a(to_integer(at(vector_prefix, a)), to_integer(at(vector_prefix, a_vec.0[0])), to_integer(at(vector_prefix, a_vec.0[1])), to_integer(at(vector_prefix, a_vec.0[2])), to_integer(at(vector_prefix, a_vec.0[3]))), 65521) == adler_spec_a(bytes, (((bytes.len() - bytes.len() % 4u64) as u32) as i32), to_integer(at(vector_prefix, a)));
     have 0 <= to_integer((at(vector_prefix, a)));
     have to_integer((at(vector_prefix, a))) <= 4294967295;
     have 0 <= to_integer((at(vector_prefix, a_vec.0[0])));
     have to_integer((at(vector_prefix, a_vec.0[0]))) <= 4294967295;
     have 0 <= to_integer((at(vector_prefix, a_vec.0[1])));
     have to_integer((at(vector_prefix, a_vec.0[1]))) <= 4294967295;
     have 0 <= to_integer((at(vector_prefix, a_vec.0[2])));
     have to_integer((at(vector_prefix, a_vec.0[2]))) <= 4294967295;
     have 0 <= to_integer((at(vector_prefix, a_vec.0[3])));
     have to_integer((at(vector_prefix, a_vec.0[3]))) <= 4294967295;
     apply(adler_lane_a_reduction(to_integer(at(vector_prefix, a)), to_integer(at(vector_prefix, a_vec.0[0])), to_integer(at(vector_prefix, a_vec.0[1])), to_integer(at(vector_prefix, a_vec.0[2])), to_integer(at(vector_prefix, a_vec.0[3]))));
     have to_integer(remainder_len) == to_integer(bytes.len() - (bytes.len() - bytes.len() % 4u64)) by close() using {};
     have remainder_len == bytes.len() % 4u64 by { apply(adler_small_tail_metadata(bytes.len())); close() using { to_integer(remainder_len) == to_integer(bytes.len() - (bytes.len() - bytes.len() % 4u64)); to_integer(bytes.len() - (bytes.len() - bytes.len() % 4u64)) == to_integer(bytes.len() % 4u64); }; }
     step_until(assignment(__rust_mir_80, 0).entry); step();
     have __rust_mir_77 == (remainder_chunk_len as u32);
     have remainder_chunk_len == bytes.len() - bytes.len() % 4u64 by close();
     apply(adler_small_length_cast(bytes.len() - bytes.len() % 4u64));
     have __rust_mir_77 <= 22204u32 by { rewrite(__rust_mir_77, (remainder_chunk_len as u32)); rewrite(remainder_chunk_len, bytes.len() - bytes.len() % 4u64); close(); }
     have __rust_mir_80 <= 65520u32 by close() using { a <= 65520u32; };
     apply(adler_scalar_batch_product_bound(__rust_mir_77, __rust_mir_80));
     have to_integer(__rust_mir_77) * to_integer(__rust_mir_80) <= 4294967295 by close() using { to_integer(__rust_mir_77) * to_integer(__rust_mir_80) <= 1454806080; };
     have __rust_mir_80 == 0u32 or __rust_mir_77 <= 4294967295u32 / __rust_mir_80 by { apply(integer::uint32_multiply_guard_by_integer_bound(__rust_mir_77, __rust_mir_80)); }
     have to_integer(bytes.len() - bytes.len() % 4u64) <= to_integer(22208u64) by close() using { to_integer(bytes.len() - bytes.len() % 4u64) <= to_integer(22204u64); };
     apply(adler_count_observation(bytes.len() - bytes.len() % 4u64));
     have __rust_mir_77 == ((bytes.len() - bytes.len() % 4u64) as u32) by close() using { __rust_mir_77 == (remainder_chunk_len as u32); to_integer(remainder_chunk_len) == to_integer(bytes.len() - bytes.len() % 4u64); };
     have to_integer(__rust_mir_77) == to_integer(((bytes.len() - bytes.len() % 4u64) as u32)) by close() using { __rust_mir_77 == ((bytes.len() - bytes.len() % 4u64) as u32); };
     have to_integer(__rust_mir_77) == to_integer((((bytes.len() - bytes.len() % 4u64) as u32) as i32)) by close() using { to_integer(__rust_mir_77) == to_integer(((bytes.len() - bytes.len() % 4u64) as u32)); to_integer(((bytes.len() - bytes.len() % 4u64) as u32)) == to_integer(bytes.len() - bytes.len() % 4u64); to_integer((((bytes.len() - bytes.len() % 4u64) as u32) as i32)) == to_integer(bytes.len() - bytes.len() % 4u64); };
     mark seed_product;
     have to_integer(at(seed_product, __rust_mir_77)) == to_integer((((bytes.len() - bytes.len() % 4u64) as u32) as i32));
     have to_integer(at(seed_product, __rust_mir_80)) == to_integer(at(vector_prefix, a));
     have to_integer(at(seed_product, __rust_mir_77)) * to_integer(at(seed_product, __rust_mir_80)) <= 1454806080 by close() using { to_integer(__rust_mir_77) * to_integer(__rust_mir_80) <= 1454806080; };
     have at(seed_product, __rust_mir_80) == 0u32 or at(seed_product, __rust_mir_77) <= 4294967295u32 / at(seed_product, __rust_mir_80) by close() using { __rust_mir_80 == 0u32 or __rust_mir_77 <= 4294967295u32 / __rust_mir_80; };
     have to_integer((at(seed_product, __rust_mir_77)) * (at(seed_product, __rust_mir_80))) == to_integer((at(seed_product, __rust_mir_77))) * to_integer((at(seed_product, __rust_mir_80))) by { have to_integer(at(seed_product, __rust_mir_77)) * to_integer(at(seed_product, __rust_mir_80)) <= 4294967295 by close() using { to_integer(at(seed_product, __rust_mir_77)) * to_integer(at(seed_product, __rust_mir_80)) <= 1454806080; }; apply(integer::uint32_multiply_to_integer(at(seed_product, __rust_mir_77), at(seed_product, __rust_mir_80))); }
     if __rust_mir_80 == 0u32 {
      step_until(assignment(__rust_mir_76, 0).entry); step();
     } else {
      have __rust_mir_77 <= 4294967295u32 / __rust_mir_80 by {
       cases {
        __rust_mir_80 == 0u32 => { contradiction(not (__rust_mir_80 == 0u32)); }
        __rust_mir_77 <= 4294967295u32 / __rust_mir_80 => { close(); }
       }
      }
      step_until(assignment(__rust_mir_76, 0).entry); step();
     }
     have __rust_mir_76 == at(seed_product, __rust_mir_77) * at(seed_product, __rust_mir_80);
     have to_integer(__rust_mir_76) == to_integer((((bytes.len() - bytes.len() % 4u64) as u32) as i32)) * to_integer(at(vector_prefix, a)) by close() using { __rust_mir_76 == at(seed_product, __rust_mir_77) * at(seed_product, __rust_mir_80); to_integer(at(seed_product, __rust_mir_77)) == to_integer((((bytes.len() - bytes.len() % 4u64) as u32) as i32)); to_integer(at(seed_product, __rust_mir_80)) == to_integer(at(vector_prefix, a)); };
     have to_integer(__rust_mir_76) <= 1454806080 by close() using { __rust_mir_76 == at(seed_product, __rust_mir_77) * at(seed_product, __rust_mir_80); to_integer(at(seed_product, __rust_mir_77)) * to_integer(at(seed_product, __rust_mir_80)) <= 1454806080; };
     have b <= 65520u32 by close();
     have to_integer(b) <= to_integer(65520u32);
     have to_integer(b) + to_integer(__rust_mir_76) <= 4294967295 by close() using { to_integer(b) <= 65520; to_integer(__rust_mir_76) <= 1454806080; };
     have to_integer(b as int64) == to_integer(b) by close() using {};
     have to_integer(__rust_mir_76 as int64) == to_integer(__rust_mir_76) by close() using {};
     have to_integer(b as int64 + __rust_mir_76 as int64) == to_integer(b as int64) + to_integer(__rust_mir_76 as int64) by close() using { to_integer(b as int64) == to_integer(b); to_integer(__rust_mir_76 as int64) == to_integer(__rust_mir_76); to_integer(b) + to_integer(__rust_mir_76) <= 4294967295; };
     have to_integer(b as int64 + __rust_mir_76 as int64) <= 4294967295 by close() using { to_integer(b as int64 + __rust_mir_76 as int64) == to_integer(b as int64) + to_integer(__rust_mir_76 as int64); to_integer(b as int64) == to_integer(b); to_integer(__rust_mir_76 as int64) == to_integer(__rust_mir_76); to_integer(b) + to_integer(__rust_mir_76) <= 4294967295; };
     have b <= 4294967295u32 - __rust_mir_76 by close() using { to_integer(b) + to_integer(__rust_mir_76) <= 4294967295; };
     mark deferred_b;
     have to_integer(at(deferred_b, b)) == to_integer(at(vector_prefix, b));
     have to_integer(at(deferred_b, __rust_mir_76)) == to_integer((((bytes.len() - bytes.len() % 4u64) as u32) as i32)) * to_integer(at(vector_prefix, a));
     have to_integer(at(deferred_b, b)) + to_integer(at(deferred_b, __rust_mir_76)) <= 4294967295 by close() using { to_integer(b) + to_integer(__rust_mir_76) <= 4294967295; };
     have to_integer(at(deferred_b, b) + at(deferred_b, __rust_mir_76)) == to_integer(at(deferred_b, b)) + to_integer(at(deferred_b, __rust_mir_76));
     step_until(assignment(__rust_mir_84, 0).entry); step();
     mark reduction_a;
     have to_integer(at(reduction_a, a_vec.0[0])) == to_integer(at(vector_prefix, a_vec.0[0]));
     have to_integer(at(reduction_a, a_vec.0[1])) == to_integer(at(vector_prefix, a_vec.0[1]));
     have to_integer(at(reduction_a, a_vec.0[2])) == to_integer(at(vector_prefix, a_vec.0[2]));
     have to_integer(at(reduction_a, a_vec.0[3])) == to_integer(at(vector_prefix, a_vec.0[3]));
     step_until(assignment(__rust_mir_86, 0).entry); step();
     mark reduction_b;
     have to_integer(at(reduction_b, b_vec.0[0])) == to_integer(at(vector_prefix, b_vec.0[0]));
     have to_integer(at(reduction_b, b_vec.0[1])) == to_integer(at(vector_prefix, b_vec.0[1]));
     have to_integer(at(reduction_b, b_vec.0[2])) == to_integer(at(vector_prefix, b_vec.0[2]));
     have to_integer(at(reduction_b, b_vec.0[3])) == to_integer(at(vector_prefix, b_vec.0[3]));
     step_until(assignment(__rust_mir_88, 0).entry);
     have __rust_checked_77 == at(deferred_b, b) + at(deferred_b, __rust_mir_76);
     have to_integer(__rust_checked_77) == to_integer(at(deferred_b, b) + at(deferred_b, __rust_mir_76)) by close() using { __rust_checked_77 == at(deferred_b, b) + at(deferred_b, __rust_mir_76); };
     have to_integer(__rust_checked_77) == to_integer(at(vector_prefix, b)) + to_integer((((bytes.len() - bytes.len() % 4u64) as u32) as i32)) * to_integer(at(vector_prefix, a)) by close() using { to_integer(__rust_checked_77) == to_integer(at(deferred_b, b) + at(deferred_b, __rust_mir_76)); to_integer(at(deferred_b, b) + at(deferred_b, __rust_mir_76)) == to_integer(at(deferred_b, b)) + to_integer(at(deferred_b, __rust_mir_76)); to_integer(at(deferred_b, b)) == to_integer(at(vector_prefix, b)); to_integer(at(deferred_b, __rust_mir_76)) == to_integer((((bytes.len() - bytes.len() % 4u64) as u32) as i32)) * to_integer(at(vector_prefix, a)); };

     have 0 <= to_integer(__rust_checked_77);
     have to_integer(__rust_checked_77) <= 4294967295;
     have 0 <= to_integer(at(vector_prefix, b)) + to_integer((((bytes.len() - bytes.len() % 4u64) as u32) as i32)) * to_integer(at(vector_prefix, a)) by close() using { 0 <= to_integer(__rust_checked_77); to_integer(__rust_checked_77) == to_integer(at(vector_prefix, b)) + to_integer((((bytes.len() - bytes.len() % 4u64) as u32) as i32)) * to_integer(at(vector_prefix, a)); };
     have 0 <= to_integer((at(vector_prefix, b_vec.0[0])));
     have to_integer((at(vector_prefix, b_vec.0[0]))) <= 4294967295;
     have 0 <= to_integer((at(vector_prefix, b_vec.0[1])));
     have to_integer((at(vector_prefix, b_vec.0[1]))) <= 4294967295;
     have 0 <= to_integer((at(vector_prefix, b_vec.0[2])));
     have to_integer((at(vector_prefix, b_vec.0[2]))) <= 4294967295;
     have 0 <= to_integer((at(vector_prefix, b_vec.0[3])));
     have to_integer((at(vector_prefix, b_vec.0[3]))) <= 4294967295;
     apply(adler_lane_b_reduction(to_integer(at(vector_prefix, b)) + to_integer((((bytes.len() - bytes.len() % 4u64) as u32) as i32)) * to_integer(at(vector_prefix, a)), to_integer(at(vector_prefix, a_vec.0[1])), to_integer(at(vector_prefix, a_vec.0[2])), to_integer(at(vector_prefix, a_vec.0[3])), to_integer(at(vector_prefix, b_vec.0[0])), to_integer(at(vector_prefix, b_vec.0[1])), to_integer(at(vector_prefix, b_vec.0[2])), to_integer(at(vector_prefix, b_vec.0[3]))));
     have __rust_checked_82 == 65521u32;
     have 65521u32 == __rust_checked_82 by close() using { __rust_checked_82 == 65521u32; };
     have b_vec.0[0] < __rust_checked_82;
     have b_vec.0[0] < 65521u32 by { rewrite(65521u32, __rust_checked_82); close(); }
     have b_vec.0[0] <= 4294967295u32 / 4u32 by close() using { b_vec.0[0] < 65521u32; };
     have b_vec.0[1] < __rust_checked_82;
     have b_vec.0[1] < 65521u32 by { rewrite(65521u32, __rust_checked_82); close(); }
     have b_vec.0[1] <= 4294967295u32 / 4u32 by close() using { b_vec.0[1] < 65521u32; };
     have b_vec.0[2] < __rust_checked_82;
     have b_vec.0[2] < 65521u32 by { rewrite(65521u32, __rust_checked_82); close(); }
     have b_vec.0[2] <= 4294967295u32 / 4u32 by close() using { b_vec.0[2] < 65521u32; };
     have b_vec.0[3] < __rust_checked_82;
     have b_vec.0[3] < 65521u32 by { rewrite(65521u32, __rust_checked_82); close(); }
     have b_vec.0[3] <= 4294967295u32 / 4u32 by close() using { b_vec.0[3] < 65521u32; };
     have to_integer((b_vec.0[0])) < to_integer(65521u32);
     have to_integer(b_vec.0[0]) <= 65520 by close() using { to_integer(b_vec.0[0]) < 65521; };
     have to_integer((b_vec.0[1])) < to_integer(65521u32);
     have to_integer(b_vec.0[1]) <= 65520 by close() using { to_integer(b_vec.0[1]) < 65521; };
     have to_integer((b_vec.0[2])) < to_integer(65521u32);
     have to_integer(b_vec.0[2]) <= 65520 by close() using { to_integer(b_vec.0[2]) < 65521; };
     have to_integer((b_vec.0[3])) < to_integer(65521u32);
     have to_integer(b_vec.0[3]) <= 65520 by close() using { to_integer(b_vec.0[3]) < 65521; };
     have to_integer(a) == to_integer(at(vector_prefix, a));
     have __rust_checked_84 == 65521u32;
     have a_vec.0[0] == at(reduction_a, a_vec.0[0]) % __rust_checked_84;
     have a_vec.0[0] == at(reduction_a, a_vec.0[0]) % 65521u32 by { rewrite(a_vec.0[0], at(reduction_a, a_vec.0[0]) % __rust_checked_84); close() using { __rust_checked_84 == 65521u32; }; }
     have to_integer((at(reduction_a, a_vec.0[0])) % 65521u32) == truncating_remainder(to_integer((at(reduction_a, a_vec.0[0]))), to_integer(65521u32)) by { apply(integer::uint32_remainder_to_integer((at(reduction_a, a_vec.0[0])), 65521u32)); }
     have to_integer(a_vec.0[0]) == to_integer(at(reduction_a, a_vec.0[0]) % 65521u32) by close() using { a_vec.0[0] == at(reduction_a, a_vec.0[0]) % 65521u32; };
     have truncating_remainder(to_integer(at(reduction_a, a_vec.0[0])), 65521) == truncating_remainder(to_integer(at(vector_prefix, a_vec.0[0])), 65521) by { rewrite(to_integer(at(reduction_a, a_vec.0[0])), to_integer(at(vector_prefix, a_vec.0[0]))); close(); }
     have to_integer(a_vec.0[0]) == truncating_remainder(to_integer(at(vector_prefix, a_vec.0[0])), 65521) by close() using { to_integer(a_vec.0[0]) == to_integer(at(reduction_a, a_vec.0[0]) % 65521u32); to_integer(at(reduction_a, a_vec.0[0]) % 65521u32) == truncating_remainder(to_integer(at(reduction_a, a_vec.0[0])), to_integer(65521u32)); truncating_remainder(to_integer(at(reduction_a, a_vec.0[0])), 65521) == truncating_remainder(to_integer(at(vector_prefix, a_vec.0[0])), 65521); };
     have a_vec.0[1] == at(reduction_a, a_vec.0[1]) % __rust_checked_84;
     have a_vec.0[1] == at(reduction_a, a_vec.0[1]) % 65521u32 by { rewrite(a_vec.0[1], at(reduction_a, a_vec.0[1]) % __rust_checked_84); close() using { __rust_checked_84 == 65521u32; }; }
     have to_integer((at(reduction_a, a_vec.0[1])) % 65521u32) == truncating_remainder(to_integer((at(reduction_a, a_vec.0[1]))), to_integer(65521u32)) by { apply(integer::uint32_remainder_to_integer((at(reduction_a, a_vec.0[1])), 65521u32)); }
     have to_integer(a_vec.0[1]) == to_integer(at(reduction_a, a_vec.0[1]) % 65521u32) by close() using { a_vec.0[1] == at(reduction_a, a_vec.0[1]) % 65521u32; };
     have truncating_remainder(to_integer(at(reduction_a, a_vec.0[1])), 65521) == truncating_remainder(to_integer(at(vector_prefix, a_vec.0[1])), 65521) by { rewrite(to_integer(at(reduction_a, a_vec.0[1])), to_integer(at(vector_prefix, a_vec.0[1]))); close(); }
     have to_integer(a_vec.0[1]) == truncating_remainder(to_integer(at(vector_prefix, a_vec.0[1])), 65521) by close() using { to_integer(a_vec.0[1]) == to_integer(at(reduction_a, a_vec.0[1]) % 65521u32); to_integer(at(reduction_a, a_vec.0[1]) % 65521u32) == truncating_remainder(to_integer(at(reduction_a, a_vec.0[1])), to_integer(65521u32)); truncating_remainder(to_integer(at(reduction_a, a_vec.0[1])), 65521) == truncating_remainder(to_integer(at(vector_prefix, a_vec.0[1])), 65521); };
     have a_vec.0[2] == at(reduction_a, a_vec.0[2]) % __rust_checked_84;
     have a_vec.0[2] == at(reduction_a, a_vec.0[2]) % 65521u32 by { rewrite(a_vec.0[2], at(reduction_a, a_vec.0[2]) % __rust_checked_84); close() using { __rust_checked_84 == 65521u32; }; }
     have to_integer((at(reduction_a, a_vec.0[2])) % 65521u32) == truncating_remainder(to_integer((at(reduction_a, a_vec.0[2]))), to_integer(65521u32)) by { apply(integer::uint32_remainder_to_integer((at(reduction_a, a_vec.0[2])), 65521u32)); }
     have to_integer(a_vec.0[2]) == to_integer(at(reduction_a, a_vec.0[2]) % 65521u32) by close() using { a_vec.0[2] == at(reduction_a, a_vec.0[2]) % 65521u32; };
     have truncating_remainder(to_integer(at(reduction_a, a_vec.0[2])), 65521) == truncating_remainder(to_integer(at(vector_prefix, a_vec.0[2])), 65521) by { rewrite(to_integer(at(reduction_a, a_vec.0[2])), to_integer(at(vector_prefix, a_vec.0[2]))); close(); }
     have to_integer(a_vec.0[2]) == truncating_remainder(to_integer(at(vector_prefix, a_vec.0[2])), 65521) by close() using { to_integer(a_vec.0[2]) == to_integer(at(reduction_a, a_vec.0[2]) % 65521u32); to_integer(at(reduction_a, a_vec.0[2]) % 65521u32) == truncating_remainder(to_integer(at(reduction_a, a_vec.0[2])), to_integer(65521u32)); truncating_remainder(to_integer(at(reduction_a, a_vec.0[2])), 65521) == truncating_remainder(to_integer(at(vector_prefix, a_vec.0[2])), 65521); };
     have a_vec.0[3] == at(reduction_a, a_vec.0[3]) % __rust_checked_84;
     have a_vec.0[3] == at(reduction_a, a_vec.0[3]) % 65521u32 by { rewrite(a_vec.0[3], at(reduction_a, a_vec.0[3]) % __rust_checked_84); close() using { __rust_checked_84 == 65521u32; }; }
     have to_integer((at(reduction_a, a_vec.0[3])) % 65521u32) == truncating_remainder(to_integer((at(reduction_a, a_vec.0[3]))), to_integer(65521u32)) by { apply(integer::uint32_remainder_to_integer((at(reduction_a, a_vec.0[3])), 65521u32)); }
     have to_integer(a_vec.0[3]) == to_integer(at(reduction_a, a_vec.0[3]) % 65521u32) by close() using { a_vec.0[3] == at(reduction_a, a_vec.0[3]) % 65521u32; };
     have truncating_remainder(to_integer(at(reduction_a, a_vec.0[3])), 65521) == truncating_remainder(to_integer(at(vector_prefix, a_vec.0[3])), 65521) by { rewrite(to_integer(at(reduction_a, a_vec.0[3])), to_integer(at(vector_prefix, a_vec.0[3]))); close(); }
     have to_integer(a_vec.0[3]) == truncating_remainder(to_integer(at(vector_prefix, a_vec.0[3])), 65521) by close() using { to_integer(a_vec.0[3]) == to_integer(at(reduction_a, a_vec.0[3]) % 65521u32); to_integer(at(reduction_a, a_vec.0[3]) % 65521u32) == truncating_remainder(to_integer(at(reduction_a, a_vec.0[3])), to_integer(65521u32)); truncating_remainder(to_integer(at(reduction_a, a_vec.0[3])), 65521) == truncating_remainder(to_integer(at(vector_prefix, a_vec.0[3])), 65521); };
     have truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521) == adler_spec_a(bytes, (((bytes.len() - bytes.len() % 4u64) as u32) as i32), to_integer(at(vector_prefix, a))) by { rewrite(to_integer(a), to_integer(at(vector_prefix, a))); rewrite(to_integer(a_vec.0[0]), truncating_remainder(to_integer(at(vector_prefix, a_vec.0[0])), 65521)); rewrite(to_integer(a_vec.0[1]), truncating_remainder(to_integer(at(vector_prefix, a_vec.0[1])), 65521)); rewrite(to_integer(a_vec.0[2]), truncating_remainder(to_integer(at(vector_prefix, a_vec.0[2])), 65521)); rewrite(to_integer(a_vec.0[3]), truncating_remainder(to_integer(at(vector_prefix, a_vec.0[3])), 65521)); close() using { truncating_remainder(adler_lane_a(to_integer(at(vector_prefix, a)), to_integer(at(vector_prefix, a_vec.0[0])), to_integer(at(vector_prefix, a_vec.0[1])), to_integer(at(vector_prefix, a_vec.0[2])), to_integer(at(vector_prefix, a_vec.0[3]))), 65521) == truncating_remainder(adler_lane_a(to_integer(at(vector_prefix, a)), truncating_remainder(to_integer(at(vector_prefix, a_vec.0[0])), 65521), truncating_remainder(to_integer(at(vector_prefix, a_vec.0[1])), 65521), truncating_remainder(to_integer(at(vector_prefix, a_vec.0[2])), 65521), truncating_remainder(to_integer(at(vector_prefix, a_vec.0[3])), 65521)), 65521); truncating_remainder(adler_lane_a(to_integer(at(vector_prefix, a)), to_integer(at(vector_prefix, a_vec.0[0])), to_integer(at(vector_prefix, a_vec.0[1])), to_integer(at(vector_prefix, a_vec.0[2])), to_integer(at(vector_prefix, a_vec.0[3]))), 65521) == adler_spec_a(bytes, (((bytes.len() - bytes.len() % 4u64) as u32) as i32), to_integer(at(vector_prefix, a))); }; }
     have b_vec.0[0] == at(reduction_b, b_vec.0[0]) % __rust_checked_82;
     have b_vec.0[0] == at(reduction_b, b_vec.0[0]) % 65521u32 by { rewrite(b_vec.0[0], at(reduction_b, b_vec.0[0]) % __rust_checked_82); close() using { __rust_checked_82 == 65521u32; }; }
     have to_integer((at(reduction_b, b_vec.0[0])) % 65521u32) == truncating_remainder(to_integer((at(reduction_b, b_vec.0[0]))), to_integer(65521u32)) by { apply(integer::uint32_remainder_to_integer((at(reduction_b, b_vec.0[0])), 65521u32)); }
     have to_integer(b_vec.0[0]) == to_integer(at(reduction_b, b_vec.0[0]) % 65521u32) by close() using { b_vec.0[0] == at(reduction_b, b_vec.0[0]) % 65521u32; };
     have truncating_remainder(to_integer(at(reduction_b, b_vec.0[0])), 65521) == truncating_remainder(to_integer(at(vector_prefix, b_vec.0[0])), 65521) by { rewrite(to_integer(at(reduction_b, b_vec.0[0])), to_integer(at(vector_prefix, b_vec.0[0]))); close(); }
     have to_integer(b_vec.0[0]) == truncating_remainder(to_integer(at(vector_prefix, b_vec.0[0])), 65521) by close() using { to_integer(b_vec.0[0]) == to_integer(at(reduction_b, b_vec.0[0]) % 65521u32); to_integer(at(reduction_b, b_vec.0[0]) % 65521u32) == truncating_remainder(to_integer(at(reduction_b, b_vec.0[0])), to_integer(65521u32)); truncating_remainder(to_integer(at(reduction_b, b_vec.0[0])), 65521) == truncating_remainder(to_integer(at(vector_prefix, b_vec.0[0])), 65521); };
     have b_vec.0[1] == at(reduction_b, b_vec.0[1]) % __rust_checked_82;
     have b_vec.0[1] == at(reduction_b, b_vec.0[1]) % 65521u32 by { rewrite(b_vec.0[1], at(reduction_b, b_vec.0[1]) % __rust_checked_82); close() using { __rust_checked_82 == 65521u32; }; }
     have to_integer((at(reduction_b, b_vec.0[1])) % 65521u32) == truncating_remainder(to_integer((at(reduction_b, b_vec.0[1]))), to_integer(65521u32)) by { apply(integer::uint32_remainder_to_integer((at(reduction_b, b_vec.0[1])), 65521u32)); }
     have to_integer(b_vec.0[1]) == to_integer(at(reduction_b, b_vec.0[1]) % 65521u32) by close() using { b_vec.0[1] == at(reduction_b, b_vec.0[1]) % 65521u32; };
     have truncating_remainder(to_integer(at(reduction_b, b_vec.0[1])), 65521) == truncating_remainder(to_integer(at(vector_prefix, b_vec.0[1])), 65521) by { rewrite(to_integer(at(reduction_b, b_vec.0[1])), to_integer(at(vector_prefix, b_vec.0[1]))); close(); }
     have to_integer(b_vec.0[1]) == truncating_remainder(to_integer(at(vector_prefix, b_vec.0[1])), 65521) by close() using { to_integer(b_vec.0[1]) == to_integer(at(reduction_b, b_vec.0[1]) % 65521u32); to_integer(at(reduction_b, b_vec.0[1]) % 65521u32) == truncating_remainder(to_integer(at(reduction_b, b_vec.0[1])), to_integer(65521u32)); truncating_remainder(to_integer(at(reduction_b, b_vec.0[1])), 65521) == truncating_remainder(to_integer(at(vector_prefix, b_vec.0[1])), 65521); };
     have b_vec.0[2] == at(reduction_b, b_vec.0[2]) % __rust_checked_82;
     have b_vec.0[2] == at(reduction_b, b_vec.0[2]) % 65521u32 by { rewrite(b_vec.0[2], at(reduction_b, b_vec.0[2]) % __rust_checked_82); close() using { __rust_checked_82 == 65521u32; }; }
     have to_integer((at(reduction_b, b_vec.0[2])) % 65521u32) == truncating_remainder(to_integer((at(reduction_b, b_vec.0[2]))), to_integer(65521u32)) by { apply(integer::uint32_remainder_to_integer((at(reduction_b, b_vec.0[2])), 65521u32)); }
     have to_integer(b_vec.0[2]) == to_integer(at(reduction_b, b_vec.0[2]) % 65521u32) by close() using { b_vec.0[2] == at(reduction_b, b_vec.0[2]) % 65521u32; };
     have truncating_remainder(to_integer(at(reduction_b, b_vec.0[2])), 65521) == truncating_remainder(to_integer(at(vector_prefix, b_vec.0[2])), 65521) by { rewrite(to_integer(at(reduction_b, b_vec.0[2])), to_integer(at(vector_prefix, b_vec.0[2]))); close(); }
     have to_integer(b_vec.0[2]) == truncating_remainder(to_integer(at(vector_prefix, b_vec.0[2])), 65521) by close() using { to_integer(b_vec.0[2]) == to_integer(at(reduction_b, b_vec.0[2]) % 65521u32); to_integer(at(reduction_b, b_vec.0[2]) % 65521u32) == truncating_remainder(to_integer(at(reduction_b, b_vec.0[2])), to_integer(65521u32)); truncating_remainder(to_integer(at(reduction_b, b_vec.0[2])), 65521) == truncating_remainder(to_integer(at(vector_prefix, b_vec.0[2])), 65521); };
     have b_vec.0[3] == at(reduction_b, b_vec.0[3]) % __rust_checked_82;
     have b_vec.0[3] == at(reduction_b, b_vec.0[3]) % 65521u32 by { rewrite(b_vec.0[3], at(reduction_b, b_vec.0[3]) % __rust_checked_82); close() using { __rust_checked_82 == 65521u32; }; }
     have to_integer((at(reduction_b, b_vec.0[3])) % 65521u32) == truncating_remainder(to_integer((at(reduction_b, b_vec.0[3]))), to_integer(65521u32)) by { apply(integer::uint32_remainder_to_integer((at(reduction_b, b_vec.0[3])), 65521u32)); }
     have to_integer(b_vec.0[3]) == to_integer(at(reduction_b, b_vec.0[3]) % 65521u32) by close() using { b_vec.0[3] == at(reduction_b, b_vec.0[3]) % 65521u32; };
     have truncating_remainder(to_integer(at(reduction_b, b_vec.0[3])), 65521) == truncating_remainder(to_integer(at(vector_prefix, b_vec.0[3])), 65521) by { rewrite(to_integer(at(reduction_b, b_vec.0[3])), to_integer(at(vector_prefix, b_vec.0[3]))); close(); }
     have to_integer(b_vec.0[3]) == truncating_remainder(to_integer(at(vector_prefix, b_vec.0[3])), 65521) by close() using { to_integer(b_vec.0[3]) == to_integer(at(reduction_b, b_vec.0[3]) % 65521u32); to_integer(at(reduction_b, b_vec.0[3]) % 65521u32) == truncating_remainder(to_integer(at(reduction_b, b_vec.0[3])), to_integer(65521u32)); truncating_remainder(to_integer(at(reduction_b, b_vec.0[3])), 65521) == truncating_remainder(to_integer(at(vector_prefix, b_vec.0[3])), 65521); };
     have __rust_checked_79 == 65521u32;
     have b == __rust_checked_77 % __rust_checked_79;
     have b == __rust_checked_77 % 65521u32 by { rewrite(b, __rust_checked_77 % __rust_checked_79); close() using { __rust_checked_79 == 65521u32; }; }
     have to_integer(__rust_checked_77 % 65521u32) == truncating_remainder(to_integer(__rust_checked_77), to_integer(65521u32)) by { apply(integer::uint32_remainder_to_integer(__rust_checked_77, 65521u32)); }
     have to_integer(b) == to_integer(__rust_checked_77 % 65521u32) by close() using { b == __rust_checked_77 % 65521u32; };
     have truncating_remainder(to_integer(__rust_checked_77), 65521) == truncating_remainder(to_integer(at(vector_prefix, b)) + to_integer((((bytes.len() - bytes.len() % 4u64) as u32) as i32)) * to_integer(at(vector_prefix, a)), 65521) by { rewrite(to_integer(__rust_checked_77), to_integer(at(vector_prefix, b)) + to_integer((((bytes.len() - bytes.len() % 4u64) as u32) as i32)) * to_integer(at(vector_prefix, a))); close(); }
     have to_integer(b) == truncating_remainder(to_integer(at(vector_prefix, b)) + to_integer((((bytes.len() - bytes.len() % 4u64) as u32) as i32)) * to_integer(at(vector_prefix, a)), 65521) by close() using { to_integer(b) == to_integer(__rust_checked_77 % 65521u32); to_integer(__rust_checked_77 % 65521u32) == truncating_remainder(to_integer(__rust_checked_77), to_integer(65521u32)); truncating_remainder(to_integer(__rust_checked_77), 65521) == truncating_remainder(to_integer(at(vector_prefix, b)) + to_integer((((bytes.len() - bytes.len() % 4u64) as u32) as i32)) * to_integer(at(vector_prefix, a)), 65521); };
     have truncating_remainder(adler_lane_b(to_integer(b), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), 65521) == adler_spec_b(bytes, (((bytes.len() - bytes.len() % 4u64) as u32) as i32), to_integer(at(vector_prefix, a)), to_integer(at(vector_prefix, b))) by { rewrite(to_integer(b), truncating_remainder(to_integer(at(vector_prefix, b)) + to_integer((((bytes.len() - bytes.len() % 4u64) as u32) as i32)) * to_integer(at(vector_prefix, a)), 65521)); rewrite(to_integer(a_vec.0[1]), truncating_remainder(to_integer(at(vector_prefix, a_vec.0[1])), 65521)); rewrite(to_integer(a_vec.0[2]), truncating_remainder(to_integer(at(vector_prefix, a_vec.0[2])), 65521)); rewrite(to_integer(a_vec.0[3]), truncating_remainder(to_integer(at(vector_prefix, a_vec.0[3])), 65521)); rewrite(to_integer(b_vec.0[0]), truncating_remainder(to_integer(at(vector_prefix, b_vec.0[0])), 65521)); rewrite(to_integer(b_vec.0[1]), truncating_remainder(to_integer(at(vector_prefix, b_vec.0[1])), 65521)); rewrite(to_integer(b_vec.0[2]), truncating_remainder(to_integer(at(vector_prefix, b_vec.0[2])), 65521)); rewrite(to_integer(b_vec.0[3]), truncating_remainder(to_integer(at(vector_prefix, b_vec.0[3])), 65521)); close() using { truncating_remainder(adler_lane_b(to_integer(at(vector_prefix, b)) + to_integer((((bytes.len() - bytes.len() % 4u64) as u32) as i32)) * to_integer(at(vector_prefix, a)), to_integer(at(vector_prefix, a_vec.0[1])), to_integer(at(vector_prefix, a_vec.0[2])), to_integer(at(vector_prefix, a_vec.0[3])), to_integer(at(vector_prefix, b_vec.0[0])), to_integer(at(vector_prefix, b_vec.0[1])), to_integer(at(vector_prefix, b_vec.0[2])), to_integer(at(vector_prefix, b_vec.0[3]))), 65521) == truncating_remainder(adler_lane_b(truncating_remainder(to_integer(at(vector_prefix, b)) + to_integer((((bytes.len() - bytes.len() % 4u64) as u32) as i32)) * to_integer(at(vector_prefix, a)), 65521), truncating_remainder(to_integer(at(vector_prefix, a_vec.0[1])), 65521), truncating_remainder(to_integer(at(vector_prefix, a_vec.0[2])), 65521), truncating_remainder(to_integer(at(vector_prefix, a_vec.0[3])), 65521), truncating_remainder(to_integer(at(vector_prefix, b_vec.0[0])), 65521), truncating_remainder(to_integer(at(vector_prefix, b_vec.0[1])), 65521), truncating_remainder(to_integer(at(vector_prefix, b_vec.0[2])), 65521), truncating_remainder(to_integer(at(vector_prefix, b_vec.0[3])), 65521)), 65521); truncating_remainder(adler_lane_b(to_integer(at(vector_prefix, b)) + to_integer((((bytes.len() - bytes.len() % 4u64) as u32) as i32)) * to_integer(at(vector_prefix, a)), to_integer(at(vector_prefix, a_vec.0[1])), to_integer(at(vector_prefix, a_vec.0[2])), to_integer(at(vector_prefix, a_vec.0[3])), to_integer(at(vector_prefix, b_vec.0[0])), to_integer(at(vector_prefix, b_vec.0[1])), to_integer(at(vector_prefix, b_vec.0[2])), to_integer(at(vector_prefix, b_vec.0[3]))), 65521) == adler_spec_b(bytes, (((bytes.len() - bytes.len() % 4u64) as u32) as i32), to_integer(at(vector_prefix, a)), to_integer(at(vector_prefix, b))); }; }
     mark weighted_b;
     have truncating_remainder(adler_lane_b(to_integer(at(weighted_b, b)), to_integer(at(weighted_b, a_vec.0[1])), to_integer(at(weighted_b, a_vec.0[2])), to_integer(at(weighted_b, a_vec.0[3])), to_integer(at(weighted_b, b_vec.0[0])), to_integer(at(weighted_b, b_vec.0[1])), to_integer(at(weighted_b, b_vec.0[2])), to_integer(at(weighted_b, b_vec.0[3]))), 65521) == adler_spec_b(bytes, (((bytes.len() - bytes.len() % 4u64) as u32) as i32), to_integer(at(vector_prefix, a)), to_integer(at(vector_prefix, b)));
     step_until(assignment(__rust_mir_91, 0).entry);
     have __rust_checked_85 == 65521u32;
     have 65521u32 == __rust_checked_85 by close() using { __rust_checked_85 == 65521u32; };
     have a_vec.0[0] < __rust_checked_85;
     have a_vec.0[0] < 65521u32 by { rewrite(65521u32, __rust_checked_85); close(); }
     have a_vec.0[1] < __rust_checked_85;
     have a_vec.0[1] < 65521u32 by { rewrite(65521u32, __rust_checked_85); close(); }
     have a_vec.0[2] < __rust_checked_85;
     have a_vec.0[2] < 65521u32 by { rewrite(65521u32, __rust_checked_85); close(); }
     have a_vec.0[3] < __rust_checked_85;
     have a_vec.0[3] < 65521u32 by { rewrite(65521u32, __rust_checked_85); close(); }
     have to_integer(b_vec.0[0]) == to_integer(at(weighted_b, b_vec.0[0])) * 4;
     have to_integer(at(weighted_b, b_vec.0[0])) <= 65520;
     have to_integer(b_vec.0[0]) <= 262080 by close() using { to_integer(b_vec.0[0]) == to_integer(at(weighted_b, b_vec.0[0])) * 4; to_integer(at(weighted_b, b_vec.0[0])) <= 65520; };
     have to_integer(b_vec.0[1]) == to_integer(at(weighted_b, b_vec.0[1])) * 4;
     have to_integer(at(weighted_b, b_vec.0[1])) <= 65520;
     have to_integer(b_vec.0[1]) <= 262080 by close() using { to_integer(b_vec.0[1]) == to_integer(at(weighted_b, b_vec.0[1])) * 4; to_integer(at(weighted_b, b_vec.0[1])) <= 65520; };
     have to_integer(b_vec.0[2]) == to_integer(at(weighted_b, b_vec.0[2])) * 4;
     have to_integer(at(weighted_b, b_vec.0[2])) <= 65520;
     have to_integer(b_vec.0[2]) <= 262080 by close() using { to_integer(b_vec.0[2]) == to_integer(at(weighted_b, b_vec.0[2])) * 4; to_integer(at(weighted_b, b_vec.0[2])) <= 65520; };
     have to_integer(b_vec.0[3]) == to_integer(at(weighted_b, b_vec.0[3])) * 4;
     have to_integer(at(weighted_b, b_vec.0[3])) <= 65520;
     have to_integer(b_vec.0[3]) <= 262080 by close() using { to_integer(b_vec.0[3]) == to_integer(at(weighted_b, b_vec.0[3])) * 4; to_integer(at(weighted_b, b_vec.0[3])) <= 65520; };
     mark correction_b;
     have to_integer(at(correction_b, b_vec.0[1])) == to_integer(at(weighted_b, b_vec.0[1])) * 4;
     have to_integer(at(correction_b, a_vec.0[1])) == to_integer(at(weighted_b, a_vec.0[1]));
     have to_integer(at(correction_b, b_vec.0[2])) == to_integer(at(weighted_b, b_vec.0[2])) * 4;
     have to_integer(at(correction_b, a_vec.0[2])) == to_integer(at(weighted_b, a_vec.0[2]));
     have to_integer(at(correction_b, b_vec.0[3])) == to_integer(at(weighted_b, b_vec.0[3])) * 4;
     have to_integer(at(correction_b, a_vec.0[3])) == to_integer(at(weighted_b, a_vec.0[3]));
     apply(adler_recombine_lane_1(a_vec.0[1], b_vec.0[1]));
     apply(adler_recombine_lane_2(a_vec.0[2], b_vec.0[2]));
     apply(adler_recombine_lane_3(a_vec.0[3], b_vec.0[3]));
     apply(adler_recombine_difference(a_vec.0[1]));
     apply(adler_recombine_difference(a_vec.0[2]));
     have 65521u32 - a_vec.0[2] <= 4294967295u32 / 2u32 by close() using { to_integer(65521u32 - a_vec.0[2]) == 65521 - to_integer(a_vec.0[2]); to_integer(65521u32 - a_vec.0[2]) <= to_integer(65521u32); };
     apply(adler_recombine_difference(a_vec.0[3]));
     have 65521u32 - a_vec.0[3] <= 4294967295u32 / 3u32 by close() using { to_integer(65521u32 - a_vec.0[3]) == 65521 - to_integer(a_vec.0[3]); to_integer(65521u32 - a_vec.0[3]) <= to_integer(65521u32); };
     have to_integer(at(correction_b, b_vec.0[1]) + (65521u32 - at(correction_b, a_vec.0[1]))) == to_integer(at(correction_b, b_vec.0[1])) + (65521 - to_integer(at(correction_b, a_vec.0[1]))) * 1;
     have to_integer(at(correction_b, b_vec.0[2]) + ((65521u32 - at(correction_b, a_vec.0[2])) * 2u32)) == to_integer(at(correction_b, b_vec.0[2])) + (65521 - to_integer(at(correction_b, a_vec.0[2]))) * 2;
     have to_integer(at(correction_b, b_vec.0[3]) + ((65521u32 - at(correction_b, a_vec.0[3])) * 3u32)) == to_integer(at(correction_b, b_vec.0[3])) + (65521 - to_integer(at(correction_b, a_vec.0[3]))) * 3;
     step_until(assignment(__rust_mir_94, 0).entry);
     have to_integer(__rust_mir_89) == to_integer(65521u32 - at(correction_b, a_vec.0[1]));
     have __rust_mir_89 == (65521u32 - at(correction_b, a_vec.0[1])) by close() using { to_integer(65521u32 - at(correction_b, a_vec.0[1])) == 65521 - to_integer(at(correction_b, a_vec.0[1])); to_integer(__rust_mir_89) == to_integer(65521u32 - at(correction_b, a_vec.0[1])); };
     have b_vec.0[1] == at(correction_b, b_vec.0[1]);
     mark correction_add_1;
     have at(correction_add_1, __rust_mir_89) == (65521u32 - at(correction_b, a_vec.0[1]));
     have at(correction_add_1, b_vec.0[1]) == at(correction_b, b_vec.0[1]);
     step();
     have __rust_mir_94 == at(correction_add_1, b_vec.0[1]) + at(correction_add_1, __rust_mir_89);
     have __rust_mir_94 == at(correction_b, b_vec.0[1]) + (65521u32 - at(correction_b, a_vec.0[1])) by { rewrite(__rust_mir_94, at(correction_add_1, b_vec.0[1]) + at(correction_add_1, __rust_mir_89)); rewrite(at(correction_add_1, b_vec.0[1]), at(correction_b, b_vec.0[1])); rewrite(at(correction_add_1, __rust_mir_89), (65521u32 - at(correction_b, a_vec.0[1]))); close(); }
     mark correction_store_1;
     have at(correction_store_1, __rust_mir_94) == at(correction_b, b_vec.0[1]) + (65521u32 - at(correction_b, a_vec.0[1]));
     step_until(assignment(__rust_mir_102, 0).entry);
     have to_integer(__rust_mir_95) == to_integer((65521u32 - at(correction_b, a_vec.0[2])) * 2u32);
     have to_integer((65521u32 - at(correction_b, a_vec.0[2])) * 2u32) == to_integer(65521u32 - at(correction_b, a_vec.0[2])) * 2 by close() using { to_integer(65521u32 - at(correction_b, a_vec.0[2])) == 65521 - to_integer(at(correction_b, a_vec.0[2])); 0 <= to_integer(at(correction_b, a_vec.0[2])); };
     have __rust_mir_95 == ((65521u32 - at(correction_b, a_vec.0[2])) * 2u32) by close() using { to_integer(__rust_mir_95) == to_integer((65521u32 - at(correction_b, a_vec.0[2])) * 2u32); to_integer((65521u32 - at(correction_b, a_vec.0[2])) * 2u32) == to_integer(65521u32 - at(correction_b, a_vec.0[2])) * 2; to_integer(65521u32 - at(correction_b, a_vec.0[2])) == 65521 - to_integer(at(correction_b, a_vec.0[2])); };
     have b_vec.0[2] == at(correction_b, b_vec.0[2]);
     mark correction_add_2;
     have at(correction_add_2, __rust_mir_95) == ((65521u32 - at(correction_b, a_vec.0[2])) * 2u32);
     have at(correction_add_2, b_vec.0[2]) == at(correction_b, b_vec.0[2]);
     step();
     have __rust_mir_102 == at(correction_add_2, b_vec.0[2]) + at(correction_add_2, __rust_mir_95);
     have __rust_mir_102 == at(correction_b, b_vec.0[2]) + ((65521u32 - at(correction_b, a_vec.0[2])) * 2u32) by { rewrite(__rust_mir_102, at(correction_add_2, b_vec.0[2]) + at(correction_add_2, __rust_mir_95)); rewrite(at(correction_add_2, b_vec.0[2]), at(correction_b, b_vec.0[2])); rewrite(at(correction_add_2, __rust_mir_95), ((65521u32 - at(correction_b, a_vec.0[2])) * 2u32)); close(); }
     mark correction_store_2;
     have at(correction_store_2, __rust_mir_102) == at(correction_b, b_vec.0[2]) + ((65521u32 - at(correction_b, a_vec.0[2])) * 2u32);
     step_until(assignment(__rust_mir_104, 0).entry); step();
     have to_integer(__rust_mir_104) == to_integer(65521u32 - at(correction_b, a_vec.0[3]));
     have __rust_mir_104 == 65521u32 - at(correction_b, a_vec.0[3]) by close() using { to_integer(65521u32 - at(correction_b, a_vec.0[3])) == 65521 - to_integer(at(correction_b, a_vec.0[3])); to_integer(__rust_mir_104) == to_integer(65521u32 - at(correction_b, a_vec.0[3])); };
     step_until(assignment(__rust_mir_108, 0).entry);
     mark correction_multiply_3;
     have at(correction_multiply_3, __rust_mir_104) == 65521u32 - at(correction_b, a_vec.0[3]);
     step();
     have __rust_mir_108 == at(correction_multiply_3, __rust_mir_104) * 3u32;
     have __rust_mir_108 == (65521u32 - at(correction_b, a_vec.0[3])) * 3u32 by { rewrite(__rust_mir_108, at(correction_multiply_3, __rust_mir_104) * 3u32); rewrite(at(correction_multiply_3, __rust_mir_104), 65521u32 - at(correction_b, a_vec.0[3])); close(); }
     step_until(assignment(__rust_mir_103, 0).entry); step();
     have __rust_mir_103 == (65521u32 - at(correction_b, a_vec.0[3])) * 3u32 by close() using { __rust_mir_108 == (65521u32 - at(correction_b, a_vec.0[3])) * 3u32; };
     step_until(assignment(__rust_mir_110, 0).entry);
     have b_vec.0[3] == at(correction_b, b_vec.0[3]);
     mark correction_add_3;
     have at(correction_add_3, __rust_mir_103) == ((65521u32 - at(correction_b, a_vec.0[3])) * 3u32);
     have at(correction_add_3, b_vec.0[3]) == at(correction_b, b_vec.0[3]);
     step();
     have __rust_mir_110 == at(correction_add_3, b_vec.0[3]) + at(correction_add_3, __rust_mir_103);
     have __rust_mir_110 == at(correction_b, b_vec.0[3]) + ((65521u32 - at(correction_b, a_vec.0[3])) * 3u32) by { rewrite(__rust_mir_110, at(correction_add_3, b_vec.0[3]) + at(correction_add_3, __rust_mir_103)); rewrite(at(correction_add_3, b_vec.0[3]), at(correction_b, b_vec.0[3])); rewrite(at(correction_add_3, __rust_mir_103), ((65521u32 - at(correction_b, a_vec.0[3])) * 3u32)); close(); }
     mark correction_store_3;
     have at(correction_store_3, __rust_mir_110) == at(correction_b, b_vec.0[3]) + ((65521u32 - at(correction_b, a_vec.0[3])) * 3u32);
     step_until(loop(3).entry);
     have b_vec.0[1] == at(correction_store_1, __rust_mir_94);
     have b_vec.0[1] == at(correction_b, b_vec.0[1]) + (65521u32 - at(correction_b, a_vec.0[1])) by { rewrite(b_vec.0[1], at(correction_store_1, __rust_mir_94)); rewrite(at(correction_store_1, __rust_mir_94), at(correction_b, b_vec.0[1]) + (65521u32 - at(correction_b, a_vec.0[1]))); close(); }
     have to_integer(b_vec.0[1]) == to_integer(at(correction_b, b_vec.0[1]) + (65521u32 - at(correction_b, a_vec.0[1]))) by close() using { b_vec.0[1] == at(correction_b, b_vec.0[1]) + (65521u32 - at(correction_b, a_vec.0[1])); };
     have to_integer(b_vec.0[1]) == to_integer(at(weighted_b, b_vec.0[1])) * 4 + (65521 - to_integer(at(weighted_b, a_vec.0[1]))) * 1 by close() using { to_integer(b_vec.0[1]) == to_integer(at(correction_b, b_vec.0[1]) + (65521u32 - at(correction_b, a_vec.0[1]))); to_integer(at(correction_b, b_vec.0[1]) + (65521u32 - at(correction_b, a_vec.0[1]))) == to_integer(at(correction_b, b_vec.0[1])) + (65521 - to_integer(at(correction_b, a_vec.0[1]))) * 1; to_integer(at(correction_b, b_vec.0[1])) == to_integer(at(weighted_b, b_vec.0[1])) * 4; to_integer(at(correction_b, a_vec.0[1])) == to_integer(at(weighted_b, a_vec.0[1])); };
     have b_vec.0[2] == at(correction_store_2, __rust_mir_102);
     have b_vec.0[2] == at(correction_b, b_vec.0[2]) + ((65521u32 - at(correction_b, a_vec.0[2])) * 2u32) by { rewrite(b_vec.0[2], at(correction_store_2, __rust_mir_102)); rewrite(at(correction_store_2, __rust_mir_102), at(correction_b, b_vec.0[2]) + ((65521u32 - at(correction_b, a_vec.0[2])) * 2u32)); close(); }
     have to_integer(b_vec.0[2]) == to_integer(at(correction_b, b_vec.0[2]) + ((65521u32 - at(correction_b, a_vec.0[2])) * 2u32)) by close() using { b_vec.0[2] == at(correction_b, b_vec.0[2]) + ((65521u32 - at(correction_b, a_vec.0[2])) * 2u32); };
     have to_integer(b_vec.0[2]) == to_integer(at(weighted_b, b_vec.0[2])) * 4 + (65521 - to_integer(at(weighted_b, a_vec.0[2]))) * 2 by close() using { to_integer(b_vec.0[2]) == to_integer(at(correction_b, b_vec.0[2]) + ((65521u32 - at(correction_b, a_vec.0[2])) * 2u32)); to_integer(at(correction_b, b_vec.0[2]) + ((65521u32 - at(correction_b, a_vec.0[2])) * 2u32)) == to_integer(at(correction_b, b_vec.0[2])) + (65521 - to_integer(at(correction_b, a_vec.0[2]))) * 2; to_integer(at(correction_b, b_vec.0[2])) == to_integer(at(weighted_b, b_vec.0[2])) * 4; to_integer(at(correction_b, a_vec.0[2])) == to_integer(at(weighted_b, a_vec.0[2])); };
     have b_vec.0[3] == at(correction_store_3, __rust_mir_110);
     have b_vec.0[3] == at(correction_b, b_vec.0[3]) + ((65521u32 - at(correction_b, a_vec.0[3])) * 3u32) by { rewrite(b_vec.0[3], at(correction_store_3, __rust_mir_110)); rewrite(at(correction_store_3, __rust_mir_110), at(correction_b, b_vec.0[3]) + ((65521u32 - at(correction_b, a_vec.0[3])) * 3u32)); close(); }
     have to_integer(b_vec.0[3]) == to_integer(at(correction_b, b_vec.0[3]) + ((65521u32 - at(correction_b, a_vec.0[3])) * 3u32)) by close() using { b_vec.0[3] == at(correction_b, b_vec.0[3]) + ((65521u32 - at(correction_b, a_vec.0[3])) * 3u32); };
     have to_integer(b_vec.0[3]) == to_integer(at(weighted_b, b_vec.0[3])) * 4 + (65521 - to_integer(at(weighted_b, a_vec.0[3]))) * 3 by close() using { to_integer(b_vec.0[3]) == to_integer(at(correction_b, b_vec.0[3]) + ((65521u32 - at(correction_b, a_vec.0[3])) * 3u32)); to_integer(at(correction_b, b_vec.0[3]) + ((65521u32 - at(correction_b, a_vec.0[3])) * 3u32)) == to_integer(at(correction_b, b_vec.0[3])) + (65521 - to_integer(at(correction_b, a_vec.0[3]))) * 3; to_integer(at(correction_b, b_vec.0[3])) == to_integer(at(weighted_b, b_vec.0[3])) * 4; to_integer(at(correction_b, a_vec.0[3])) == to_integer(at(weighted_b, a_vec.0[3])); };
     have to_integer(b_vec.0[0]) == to_integer(at(weighted_b, b_vec.0[0])) * 4;
     have a <= 65520u32 by close();
     have to_integer(a) <= to_integer(65520u32);
     step_until(assignment(__rust_mir_121, 0).entry);
     have av == a_vec.0[0];
     have to_integer((a_vec.0[0])) < to_integer(65521u32);
     have to_integer(av) <= 65520 by { rewrite(av, a_vec.0[0]); close() using { to_integer(a_vec.0[0]) < 65521; }; }
     step();
     have to_integer(__rust_mir_121) <= 65520 by close() using { to_integer(av) <= 65520; };
     have to_integer(a) + to_integer(__rust_mir_121) <= 4294967295 by close() using { to_integer(a) <= 65520; to_integer(__rust_mir_121) <= 65520; };
     have a <= 4294967295u32 - __rust_mir_121 by close() using { to_integer(a) + to_integer(__rust_mir_121) <= 4294967295; };
     step_until(assignment(__rust_mir_122, 0).entry);
     mark small_sum_a_0;
     have to_integer(at(small_sum_a_0, a)) == to_integer(at(vector_prefix, a));
     have to_integer(at(small_sum_a_0, __rust_mir_121)) == to_integer(a_vec.0[0]);
     have to_integer(at(small_sum_a_0, a)) <= 65520 by close() using { to_integer(a) <= 65520; };
     have to_integer(at(small_sum_a_0, __rust_mir_121)) <= 65520 by close() using { to_integer(__rust_mir_121) <= 65520; };
     have to_integer(at(small_sum_a_0, a)) + to_integer(at(small_sum_a_0, __rust_mir_121)) <= 4294967295 by close() using { to_integer(at(small_sum_a_0, a)) <= 65520; to_integer(at(small_sum_a_0, __rust_mir_121)) <= 65520; };
     step();
     have to_integer(at(small_sum_a_0, a) + at(small_sum_a_0, __rust_mir_121)) == to_integer(at(small_sum_a_0, a)) + to_integer(at(small_sum_a_0, __rust_mir_121)) by { apply(integer::uint32_add_to_integer(at(small_sum_a_0, a), at(small_sum_a_0, __rust_mir_121))); }
     have to_integer(__rust_mir_122) == to_integer(at(small_sum_a_0, a) + at(small_sum_a_0, __rust_mir_121));
     have __rust_mir_122 == at(small_sum_a_0, a) + at(small_sum_a_0, __rust_mir_121) by close() using { to_integer(__rust_mir_122) == to_integer(at(small_sum_a_0, a) + at(small_sum_a_0, __rust_mir_121)); to_integer(at(small_sum_a_0, a) + at(small_sum_a_0, __rust_mir_121)) == to_integer(at(small_sum_a_0, a)) + to_integer(at(small_sum_a_0, __rust_mir_121)); };
     have to_integer(__rust_mir_122) <= 131040 by { rewrite(__rust_mir_122, at(small_sum_a_0, a) + at(small_sum_a_0, __rust_mir_121)); close() using { to_integer(at(small_sum_a_0, a)) <= 65520; to_integer(at(small_sum_a_0, __rust_mir_121)) <= 65520; }; }
     step_until(assignment(a, 1).entry); step();
     have to_integer(a) <= 131040 by close() using { to_integer(__rust_mir_122) <= 131040; };
     have to_integer(__rust_mir_122) == to_integer(at(small_sum_a_0, a)) + to_integer(at(small_sum_a_0, __rust_mir_121)) by close() using { __rust_mir_122 == at(small_sum_a_0, a) + at(small_sum_a_0, __rust_mir_121); to_integer(at(small_sum_a_0, a) + at(small_sum_a_0, __rust_mir_121)) == to_integer(at(small_sum_a_0, a)) + to_integer(at(small_sum_a_0, __rust_mir_121)); };
     have to_integer(a) == to_integer(__rust_mir_122);
     have to_integer(a) == to_integer(at(vector_prefix, a)) + to_integer(a_vec.0[0]) by close() using { to_integer(a) == to_integer(__rust_mir_122); to_integer(__rust_mir_122) == to_integer(at(small_sum_a_0, a)) + to_integer(at(small_sum_a_0, __rust_mir_121)); to_integer(at(small_sum_a_0, a)) == to_integer(at(vector_prefix, a)); to_integer(at(small_sum_a_0, __rust_mir_121)) == to_integer(a_vec.0[0]); };

     step(); step(); step(); step(); step(); step(); step(); step();
     step_until(assignment(__rust_mir_121, 0).entry);
     have av == a_vec.0[1];
     have to_integer((a_vec.0[1])) < to_integer(65521u32);
     have to_integer(av) <= 65520 by { rewrite(av, a_vec.0[1]); close() using { to_integer(a_vec.0[1]) < 65521; }; }
     step();
     have to_integer(__rust_mir_121) <= 65520 by close() using { to_integer(av) <= 65520; };
     have to_integer(a) + to_integer(__rust_mir_121) <= 4294967295 by close() using { to_integer(a) <= 131040; to_integer(__rust_mir_121) <= 65520; };
     have a <= 4294967295u32 - __rust_mir_121 by close() using { to_integer(a) + to_integer(__rust_mir_121) <= 4294967295; };
     step_until(assignment(__rust_mir_122, 0).entry);
     mark small_sum_a_1;
     have to_integer(at(small_sum_a_1, a)) == to_integer(at(vector_prefix, a)) + to_integer(a_vec.0[0]);
     have to_integer(at(small_sum_a_1, __rust_mir_121)) == to_integer(a_vec.0[1]);
     have to_integer(at(small_sum_a_1, a)) <= 131040 by close() using { to_integer(a) <= 131040; };
     have to_integer(at(small_sum_a_1, __rust_mir_121)) <= 65520 by close() using { to_integer(__rust_mir_121) <= 65520; };
     have to_integer(at(small_sum_a_1, a)) + to_integer(at(small_sum_a_1, __rust_mir_121)) <= 4294967295 by close() using { to_integer(at(small_sum_a_1, a)) <= 131040; to_integer(at(small_sum_a_1, __rust_mir_121)) <= 65520; };
     step();
     have to_integer(at(small_sum_a_1, a) + at(small_sum_a_1, __rust_mir_121)) == to_integer(at(small_sum_a_1, a)) + to_integer(at(small_sum_a_1, __rust_mir_121)) by { apply(integer::uint32_add_to_integer(at(small_sum_a_1, a), at(small_sum_a_1, __rust_mir_121))); }
     have to_integer(__rust_mir_122) == to_integer(at(small_sum_a_1, a) + at(small_sum_a_1, __rust_mir_121));
     have __rust_mir_122 == at(small_sum_a_1, a) + at(small_sum_a_1, __rust_mir_121) by close() using { to_integer(__rust_mir_122) == to_integer(at(small_sum_a_1, a) + at(small_sum_a_1, __rust_mir_121)); to_integer(at(small_sum_a_1, a) + at(small_sum_a_1, __rust_mir_121)) == to_integer(at(small_sum_a_1, a)) + to_integer(at(small_sum_a_1, __rust_mir_121)); };
     have to_integer(__rust_mir_122) <= 196560 by { rewrite(__rust_mir_122, at(small_sum_a_1, a) + at(small_sum_a_1, __rust_mir_121)); close() using { to_integer(at(small_sum_a_1, a)) <= 131040; to_integer(at(small_sum_a_1, __rust_mir_121)) <= 65520; }; }
     step_until(assignment(a, 1).entry); step();
     have to_integer(a) <= 196560 by close() using { to_integer(__rust_mir_122) <= 196560; };
     have to_integer(__rust_mir_122) == to_integer(at(small_sum_a_1, a)) + to_integer(at(small_sum_a_1, __rust_mir_121)) by close() using { __rust_mir_122 == at(small_sum_a_1, a) + at(small_sum_a_1, __rust_mir_121); to_integer(at(small_sum_a_1, a) + at(small_sum_a_1, __rust_mir_121)) == to_integer(at(small_sum_a_1, a)) + to_integer(at(small_sum_a_1, __rust_mir_121)); };
     have to_integer(a) == to_integer(__rust_mir_122);
     have to_integer(a) == to_integer(at(vector_prefix, a)) + to_integer(a_vec.0[0]) + to_integer(a_vec.0[1]) by close() using { to_integer(a) == to_integer(__rust_mir_122); to_integer(__rust_mir_122) == to_integer(at(small_sum_a_1, a)) + to_integer(at(small_sum_a_1, __rust_mir_121)); to_integer(at(small_sum_a_1, a)) == to_integer(at(vector_prefix, a)) + to_integer(a_vec.0[0]); to_integer(at(small_sum_a_1, __rust_mir_121)) == to_integer(a_vec.0[1]); };

     step(); step(); step(); step(); step(); step(); step(); step();
     step_until(assignment(__rust_mir_121, 0).entry);
     have av == a_vec.0[2];
     have to_integer((a_vec.0[2])) < to_integer(65521u32);
     have to_integer(av) <= 65520 by { rewrite(av, a_vec.0[2]); close() using { to_integer(a_vec.0[2]) < 65521; }; }
     step();
     have to_integer(__rust_mir_121) <= 65520 by close() using { to_integer(av) <= 65520; };
     have to_integer(a) + to_integer(__rust_mir_121) <= 4294967295 by close() using { to_integer(a) <= 196560; to_integer(__rust_mir_121) <= 65520; };
     have a <= 4294967295u32 - __rust_mir_121 by close() using { to_integer(a) + to_integer(__rust_mir_121) <= 4294967295; };
     step_until(assignment(__rust_mir_122, 0).entry);
     mark small_sum_a_2;
     have to_integer(at(small_sum_a_2, a)) == to_integer(at(vector_prefix, a)) + to_integer(a_vec.0[0]) + to_integer(a_vec.0[1]);
     have to_integer(at(small_sum_a_2, __rust_mir_121)) == to_integer(a_vec.0[2]);
     have to_integer(at(small_sum_a_2, a)) <= 196560 by close() using { to_integer(a) <= 196560; };
     have to_integer(at(small_sum_a_2, __rust_mir_121)) <= 65520 by close() using { to_integer(__rust_mir_121) <= 65520; };
     have to_integer(at(small_sum_a_2, a)) + to_integer(at(small_sum_a_2, __rust_mir_121)) <= 4294967295 by close() using { to_integer(at(small_sum_a_2, a)) <= 196560; to_integer(at(small_sum_a_2, __rust_mir_121)) <= 65520; };
     step();
     have to_integer(at(small_sum_a_2, a) + at(small_sum_a_2, __rust_mir_121)) == to_integer(at(small_sum_a_2, a)) + to_integer(at(small_sum_a_2, __rust_mir_121)) by { apply(integer::uint32_add_to_integer(at(small_sum_a_2, a), at(small_sum_a_2, __rust_mir_121))); }
     have to_integer(__rust_mir_122) == to_integer(at(small_sum_a_2, a) + at(small_sum_a_2, __rust_mir_121));
     have __rust_mir_122 == at(small_sum_a_2, a) + at(small_sum_a_2, __rust_mir_121) by close() using { to_integer(__rust_mir_122) == to_integer(at(small_sum_a_2, a) + at(small_sum_a_2, __rust_mir_121)); to_integer(at(small_sum_a_2, a) + at(small_sum_a_2, __rust_mir_121)) == to_integer(at(small_sum_a_2, a)) + to_integer(at(small_sum_a_2, __rust_mir_121)); };
     have to_integer(__rust_mir_122) <= 262080 by { rewrite(__rust_mir_122, at(small_sum_a_2, a) + at(small_sum_a_2, __rust_mir_121)); close() using { to_integer(at(small_sum_a_2, a)) <= 196560; to_integer(at(small_sum_a_2, __rust_mir_121)) <= 65520; }; }
     step_until(assignment(a, 1).entry); step();
     have to_integer(a) <= 262080 by close() using { to_integer(__rust_mir_122) <= 262080; };
     have to_integer(__rust_mir_122) == to_integer(at(small_sum_a_2, a)) + to_integer(at(small_sum_a_2, __rust_mir_121)) by close() using { __rust_mir_122 == at(small_sum_a_2, a) + at(small_sum_a_2, __rust_mir_121); to_integer(at(small_sum_a_2, a) + at(small_sum_a_2, __rust_mir_121)) == to_integer(at(small_sum_a_2, a)) + to_integer(at(small_sum_a_2, __rust_mir_121)); };
     have to_integer(a) == to_integer(__rust_mir_122);
     have to_integer(a) == to_integer(at(vector_prefix, a)) + to_integer(a_vec.0[0]) + to_integer(a_vec.0[1]) + to_integer(a_vec.0[2]) by close() using { to_integer(a) == to_integer(__rust_mir_122); to_integer(__rust_mir_122) == to_integer(at(small_sum_a_2, a)) + to_integer(at(small_sum_a_2, __rust_mir_121)); to_integer(at(small_sum_a_2, a)) == to_integer(at(vector_prefix, a)) + to_integer(a_vec.0[0]) + to_integer(a_vec.0[1]); to_integer(at(small_sum_a_2, __rust_mir_121)) == to_integer(a_vec.0[2]); };

     step(); step(); step(); step(); step(); step(); step(); step();
     step_until(assignment(__rust_mir_121, 0).entry);
     have av == a_vec.0[3];
     have to_integer((a_vec.0[3])) < to_integer(65521u32);
     have to_integer(av) <= 65520 by { rewrite(av, a_vec.0[3]); close() using { to_integer(a_vec.0[3]) < 65521; }; }
     step();
     have to_integer(__rust_mir_121) <= 65520 by close() using { to_integer(av) <= 65520; };
     have to_integer(a) + to_integer(__rust_mir_121) <= 4294967295 by close() using { to_integer(a) <= 262080; to_integer(__rust_mir_121) <= 65520; };
     have a <= 4294967295u32 - __rust_mir_121 by close() using { to_integer(a) + to_integer(__rust_mir_121) <= 4294967295; };
     step_until(assignment(__rust_mir_122, 0).entry);
     mark small_sum_a_3;
     have to_integer(at(small_sum_a_3, a)) == to_integer(at(vector_prefix, a)) + to_integer(a_vec.0[0]) + to_integer(a_vec.0[1]) + to_integer(a_vec.0[2]);
     have to_integer(at(small_sum_a_3, __rust_mir_121)) == to_integer(a_vec.0[3]);
     have to_integer(at(small_sum_a_3, a)) <= 262080 by close() using { to_integer(a) <= 262080; };
     have to_integer(at(small_sum_a_3, __rust_mir_121)) <= 65520 by close() using { to_integer(__rust_mir_121) <= 65520; };
     have to_integer(at(small_sum_a_3, a)) + to_integer(at(small_sum_a_3, __rust_mir_121)) <= 4294967295 by close() using { to_integer(at(small_sum_a_3, a)) <= 262080; to_integer(at(small_sum_a_3, __rust_mir_121)) <= 65520; };
     step();
     have to_integer(at(small_sum_a_3, a) + at(small_sum_a_3, __rust_mir_121)) == to_integer(at(small_sum_a_3, a)) + to_integer(at(small_sum_a_3, __rust_mir_121)) by { apply(integer::uint32_add_to_integer(at(small_sum_a_3, a), at(small_sum_a_3, __rust_mir_121))); }
     have to_integer(__rust_mir_122) == to_integer(at(small_sum_a_3, a) + at(small_sum_a_3, __rust_mir_121));
     have __rust_mir_122 == at(small_sum_a_3, a) + at(small_sum_a_3, __rust_mir_121) by close() using { to_integer(__rust_mir_122) == to_integer(at(small_sum_a_3, a) + at(small_sum_a_3, __rust_mir_121)); to_integer(at(small_sum_a_3, a) + at(small_sum_a_3, __rust_mir_121)) == to_integer(at(small_sum_a_3, a)) + to_integer(at(small_sum_a_3, __rust_mir_121)); };
     have to_integer(__rust_mir_122) <= 327600 by { rewrite(__rust_mir_122, at(small_sum_a_3, a) + at(small_sum_a_3, __rust_mir_121)); close() using { to_integer(at(small_sum_a_3, a)) <= 262080; to_integer(at(small_sum_a_3, __rust_mir_121)) <= 65520; }; }
     step_until(assignment(a, 1).entry); step();
     have to_integer(a) <= 327600 by close() using { to_integer(__rust_mir_122) <= 327600; };
     have to_integer(__rust_mir_122) == to_integer(at(small_sum_a_3, a)) + to_integer(at(small_sum_a_3, __rust_mir_121)) by close() using { __rust_mir_122 == at(small_sum_a_3, a) + at(small_sum_a_3, __rust_mir_121); to_integer(at(small_sum_a_3, a) + at(small_sum_a_3, __rust_mir_121)) == to_integer(at(small_sum_a_3, a)) + to_integer(at(small_sum_a_3, __rust_mir_121)); };
     have to_integer(a) == to_integer(__rust_mir_122);
     have to_integer(a) == to_integer(at(vector_prefix, a)) + to_integer(a_vec.0[0]) + to_integer(a_vec.0[1]) + to_integer(a_vec.0[2]) + to_integer(a_vec.0[3]) by close() using { to_integer(a) == to_integer(__rust_mir_122); to_integer(__rust_mir_122) == to_integer(at(small_sum_a_3, a)) + to_integer(at(small_sum_a_3, __rust_mir_121)); to_integer(at(small_sum_a_3, a)) == to_integer(at(vector_prefix, a)) + to_integer(a_vec.0[0]) + to_integer(a_vec.0[1]) + to_integer(a_vec.0[2]); to_integer(at(small_sum_a_3, __rust_mir_121)) == to_integer(a_vec.0[3]); };

     step(); step(); step(); step(); step(); step(); step(); step();
     have to_integer(a) == adler_lane_a(to_integer(at(vector_prefix, a)), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])) by { unfold(adler_lane_a(to_integer(at(vector_prefix, a)), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]))); close(); }
     have truncating_remainder(to_integer(a), 65521) == adler_spec_a(bytes, (((bytes.len() - bytes.len() % 4u64) as u32) as i32), to_integer(at(vector_prefix, a))) by { rewrite(to_integer(a), adler_lane_a(to_integer(at(vector_prefix, a)), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]))); close(); }
     step_until(loop(4).entry);
     have __rust_checked_79 == 65521u32;
     have 65521u32 == __rust_checked_79 by close() using { __rust_checked_79 == 65521u32; };
     have b == __rust_checked_77 % __rust_checked_79;
     have __rust_checked_79 != 0u32 by { rewrite(__rust_checked_79, 65521u32); normalize(); }
     have __rust_checked_77 % __rust_checked_79 < __rust_checked_79 by { apply(integer::uint32_remainder_less_than_divisor(__rust_checked_77, __rust_checked_79)); }
     have b < __rust_checked_79 by { rewrite(b, __rust_checked_77 % __rust_checked_79); close(); }
     have b < 65521u32 by { rewrite(65521u32, __rust_checked_79); close(); }
     have to_integer(b) < to_integer(65521u32);
     have to_integer(b) <= 65520 by close() using { to_integer(b) < 65521; };
     have to_integer(b_vec.0[0]) <= 262080;
     step_until(assignment(__rust_mir_133, 0).entry);
     have bv == b_vec.0[0];
     have to_integer(bv) <= 262080 by { rewrite(bv, b_vec.0[0]); close(); }
     step();
     have to_integer(__rust_mir_133) <= 262080 by close() using { to_integer(bv) <= 262080; };
     have to_integer(b) + to_integer(__rust_mir_133) <= 4294967295 by close() using { to_integer(b) <= 65520; to_integer(__rust_mir_133) <= 262080; };
     have b <= 4294967295u32 - __rust_mir_133 by close() using { to_integer(b) + to_integer(__rust_mir_133) <= 4294967295; };
     step_until(assignment(__rust_mir_134, 0).entry);
     mark small_sum_b_0;
     have to_integer(at(small_sum_b_0, b)) == to_integer(at(weighted_b, b));
     have to_integer(at(small_sum_b_0, __rust_mir_133)) == to_integer(b_vec.0[0]);
     have to_integer(at(small_sum_b_0, b)) <= 65520 by close() using { to_integer(b) <= 65520; };
     have to_integer(at(small_sum_b_0, __rust_mir_133)) <= 262080 by close() using { to_integer(__rust_mir_133) <= 262080; };
     have to_integer(at(small_sum_b_0, b)) + to_integer(at(small_sum_b_0, __rust_mir_133)) <= 4294967295 by close() using { to_integer(at(small_sum_b_0, b)) <= 65520; to_integer(at(small_sum_b_0, __rust_mir_133)) <= 262080; };
     step();
     have to_integer(at(small_sum_b_0, b) + at(small_sum_b_0, __rust_mir_133)) == to_integer(at(small_sum_b_0, b)) + to_integer(at(small_sum_b_0, __rust_mir_133)) by { apply(integer::uint32_add_to_integer(at(small_sum_b_0, b), at(small_sum_b_0, __rust_mir_133))); }
     have to_integer(__rust_mir_134) == to_integer(at(small_sum_b_0, b) + at(small_sum_b_0, __rust_mir_133));
     have __rust_mir_134 == at(small_sum_b_0, b) + at(small_sum_b_0, __rust_mir_133) by close() using { to_integer(__rust_mir_134) == to_integer(at(small_sum_b_0, b) + at(small_sum_b_0, __rust_mir_133)); to_integer(at(small_sum_b_0, b) + at(small_sum_b_0, __rust_mir_133)) == to_integer(at(small_sum_b_0, b)) + to_integer(at(small_sum_b_0, __rust_mir_133)); };
     have to_integer(__rust_mir_134) <= 327600 by { rewrite(__rust_mir_134, at(small_sum_b_0, b) + at(small_sum_b_0, __rust_mir_133)); close() using { to_integer(at(small_sum_b_0, b)) <= 65520; to_integer(at(small_sum_b_0, __rust_mir_133)) <= 262080; }; }
     step_until(assignment(b, 5).entry); step();
     have to_integer(b) <= 327600 by close() using { to_integer(__rust_mir_134) <= 327600; };
     have to_integer(__rust_mir_134) == to_integer(at(small_sum_b_0, b)) + to_integer(at(small_sum_b_0, __rust_mir_133)) by close() using { __rust_mir_134 == at(small_sum_b_0, b) + at(small_sum_b_0, __rust_mir_133); to_integer(at(small_sum_b_0, b) + at(small_sum_b_0, __rust_mir_133)) == to_integer(at(small_sum_b_0, b)) + to_integer(at(small_sum_b_0, __rust_mir_133)); };
     have to_integer(b) == to_integer(__rust_mir_134);
     have to_integer(b) == to_integer(at(weighted_b, b)) + to_integer(b_vec.0[0]) by close() using { to_integer(b) == to_integer(__rust_mir_134); to_integer(__rust_mir_134) == to_integer(at(small_sum_b_0, b)) + to_integer(at(small_sum_b_0, __rust_mir_133)); to_integer(at(small_sum_b_0, b)) == to_integer(at(weighted_b, b)); to_integer(at(small_sum_b_0, __rust_mir_133)) == to_integer(b_vec.0[0]); };

     step(); step(); step(); step(); step(); step(); step(); step();
     have to_integer(b_vec.0[1]) <= 327601;
     step_until(assignment(__rust_mir_133, 0).entry);
     have bv == b_vec.0[1];
     have to_integer(bv) <= 327601 by { rewrite(bv, b_vec.0[1]); close(); }
     step();
     have to_integer(__rust_mir_133) <= 327601 by close() using { to_integer(bv) <= 327601; };
     have to_integer(b) + to_integer(__rust_mir_133) <= 4294967295 by close() using { to_integer(b) <= 327600; to_integer(__rust_mir_133) <= 327601; };
     have b <= 4294967295u32 - __rust_mir_133 by close() using { to_integer(b) + to_integer(__rust_mir_133) <= 4294967295; };
     step_until(assignment(__rust_mir_134, 0).entry);
     mark small_sum_b_1;
     have to_integer(at(small_sum_b_1, b)) == to_integer(at(weighted_b, b)) + to_integer(b_vec.0[0]);
     have to_integer(at(small_sum_b_1, __rust_mir_133)) == to_integer(b_vec.0[1]);
     have to_integer(at(small_sum_b_1, b)) <= 327600 by close() using { to_integer(b) <= 327600; };
     have to_integer(at(small_sum_b_1, __rust_mir_133)) <= 327601 by close() using { to_integer(__rust_mir_133) <= 327601; };
     have to_integer(at(small_sum_b_1, b)) + to_integer(at(small_sum_b_1, __rust_mir_133)) <= 4294967295 by close() using { to_integer(at(small_sum_b_1, b)) <= 327600; to_integer(at(small_sum_b_1, __rust_mir_133)) <= 327601; };
     step();
     have to_integer(at(small_sum_b_1, b) + at(small_sum_b_1, __rust_mir_133)) == to_integer(at(small_sum_b_1, b)) + to_integer(at(small_sum_b_1, __rust_mir_133)) by { apply(integer::uint32_add_to_integer(at(small_sum_b_1, b), at(small_sum_b_1, __rust_mir_133))); }
     have to_integer(__rust_mir_134) == to_integer(at(small_sum_b_1, b) + at(small_sum_b_1, __rust_mir_133));
     have __rust_mir_134 == at(small_sum_b_1, b) + at(small_sum_b_1, __rust_mir_133) by close() using { to_integer(__rust_mir_134) == to_integer(at(small_sum_b_1, b) + at(small_sum_b_1, __rust_mir_133)); to_integer(at(small_sum_b_1, b) + at(small_sum_b_1, __rust_mir_133)) == to_integer(at(small_sum_b_1, b)) + to_integer(at(small_sum_b_1, __rust_mir_133)); };
     have to_integer(__rust_mir_134) <= 655201 by { rewrite(__rust_mir_134, at(small_sum_b_1, b) + at(small_sum_b_1, __rust_mir_133)); close() using { to_integer(at(small_sum_b_1, b)) <= 327600; to_integer(at(small_sum_b_1, __rust_mir_133)) <= 327601; }; }
     step_until(assignment(b, 5).entry); step();
     have to_integer(b) <= 655201 by close() using { to_integer(__rust_mir_134) <= 655201; };
     have to_integer(__rust_mir_134) == to_integer(at(small_sum_b_1, b)) + to_integer(at(small_sum_b_1, __rust_mir_133)) by close() using { __rust_mir_134 == at(small_sum_b_1, b) + at(small_sum_b_1, __rust_mir_133); to_integer(at(small_sum_b_1, b) + at(small_sum_b_1, __rust_mir_133)) == to_integer(at(small_sum_b_1, b)) + to_integer(at(small_sum_b_1, __rust_mir_133)); };
     have to_integer(b) == to_integer(__rust_mir_134);
     have to_integer(b) == to_integer(at(weighted_b, b)) + to_integer(b_vec.0[0]) + to_integer(b_vec.0[1]) by close() using { to_integer(b) == to_integer(__rust_mir_134); to_integer(__rust_mir_134) == to_integer(at(small_sum_b_1, b)) + to_integer(at(small_sum_b_1, __rust_mir_133)); to_integer(at(small_sum_b_1, b)) == to_integer(at(weighted_b, b)) + to_integer(b_vec.0[0]); to_integer(at(small_sum_b_1, __rust_mir_133)) == to_integer(b_vec.0[1]); };

     step(); step(); step(); step(); step(); step(); step(); step();
     have to_integer(b_vec.0[2]) <= 393122;
     step_until(assignment(__rust_mir_133, 0).entry);
     have bv == b_vec.0[2];
     have to_integer(bv) <= 393122 by { rewrite(bv, b_vec.0[2]); close(); }
     step();
     have to_integer(__rust_mir_133) <= 393122 by close() using { to_integer(bv) <= 393122; };
     have to_integer(b) + to_integer(__rust_mir_133) <= 4294967295 by close() using { to_integer(b) <= 655201; to_integer(__rust_mir_133) <= 393122; };
     have b <= 4294967295u32 - __rust_mir_133 by close() using { to_integer(b) + to_integer(__rust_mir_133) <= 4294967295; };
     step_until(assignment(__rust_mir_134, 0).entry);
     mark small_sum_b_2;
     have to_integer(at(small_sum_b_2, b)) == to_integer(at(weighted_b, b)) + to_integer(b_vec.0[0]) + to_integer(b_vec.0[1]);
     have to_integer(at(small_sum_b_2, __rust_mir_133)) == to_integer(b_vec.0[2]);
     have to_integer(at(small_sum_b_2, b)) <= 655201 by close() using { to_integer(b) <= 655201; };
     have to_integer(at(small_sum_b_2, __rust_mir_133)) <= 393122 by close() using { to_integer(__rust_mir_133) <= 393122; };
     have to_integer(at(small_sum_b_2, b)) + to_integer(at(small_sum_b_2, __rust_mir_133)) <= 4294967295 by close() using { to_integer(at(small_sum_b_2, b)) <= 655201; to_integer(at(small_sum_b_2, __rust_mir_133)) <= 393122; };
     step();
     have to_integer(at(small_sum_b_2, b) + at(small_sum_b_2, __rust_mir_133)) == to_integer(at(small_sum_b_2, b)) + to_integer(at(small_sum_b_2, __rust_mir_133)) by { apply(integer::uint32_add_to_integer(at(small_sum_b_2, b), at(small_sum_b_2, __rust_mir_133))); }
     have to_integer(__rust_mir_134) == to_integer(at(small_sum_b_2, b) + at(small_sum_b_2, __rust_mir_133));
     have __rust_mir_134 == at(small_sum_b_2, b) + at(small_sum_b_2, __rust_mir_133) by close() using { to_integer(__rust_mir_134) == to_integer(at(small_sum_b_2, b) + at(small_sum_b_2, __rust_mir_133)); to_integer(at(small_sum_b_2, b) + at(small_sum_b_2, __rust_mir_133)) == to_integer(at(small_sum_b_2, b)) + to_integer(at(small_sum_b_2, __rust_mir_133)); };
     have to_integer(__rust_mir_134) <= 1048323 by { rewrite(__rust_mir_134, at(small_sum_b_2, b) + at(small_sum_b_2, __rust_mir_133)); close() using { to_integer(at(small_sum_b_2, b)) <= 655201; to_integer(at(small_sum_b_2, __rust_mir_133)) <= 393122; }; }
     step_until(assignment(b, 5).entry); step();
     have to_integer(b) <= 1048323 by close() using { to_integer(__rust_mir_134) <= 1048323; };
     have to_integer(__rust_mir_134) == to_integer(at(small_sum_b_2, b)) + to_integer(at(small_sum_b_2, __rust_mir_133)) by close() using { __rust_mir_134 == at(small_sum_b_2, b) + at(small_sum_b_2, __rust_mir_133); to_integer(at(small_sum_b_2, b) + at(small_sum_b_2, __rust_mir_133)) == to_integer(at(small_sum_b_2, b)) + to_integer(at(small_sum_b_2, __rust_mir_133)); };
     have to_integer(b) == to_integer(__rust_mir_134);
     have to_integer(b) == to_integer(at(weighted_b, b)) + to_integer(b_vec.0[0]) + to_integer(b_vec.0[1]) + to_integer(b_vec.0[2]) by close() using { to_integer(b) == to_integer(__rust_mir_134); to_integer(__rust_mir_134) == to_integer(at(small_sum_b_2, b)) + to_integer(at(small_sum_b_2, __rust_mir_133)); to_integer(at(small_sum_b_2, b)) == to_integer(at(weighted_b, b)) + to_integer(b_vec.0[0]) + to_integer(b_vec.0[1]); to_integer(at(small_sum_b_2, __rust_mir_133)) == to_integer(b_vec.0[2]); };

     step(); step(); step(); step(); step(); step(); step(); step();
     have to_integer(b_vec.0[3]) <= 458643;
     step_until(assignment(__rust_mir_133, 0).entry);
     have bv == b_vec.0[3];
     have to_integer(bv) <= 458643 by { rewrite(bv, b_vec.0[3]); close(); }
     step();
     have to_integer(__rust_mir_133) <= 458643 by close() using { to_integer(bv) <= 458643; };
     have to_integer(b) + to_integer(__rust_mir_133) <= 4294967295 by close() using { to_integer(b) <= 1048323; to_integer(__rust_mir_133) <= 458643; };
     have b <= 4294967295u32 - __rust_mir_133 by close() using { to_integer(b) + to_integer(__rust_mir_133) <= 4294967295; };
     step_until(assignment(__rust_mir_134, 0).entry);
     mark small_sum_b_3;
     have to_integer(at(small_sum_b_3, b)) == to_integer(at(weighted_b, b)) + to_integer(b_vec.0[0]) + to_integer(b_vec.0[1]) + to_integer(b_vec.0[2]);
     have to_integer(at(small_sum_b_3, __rust_mir_133)) == to_integer(b_vec.0[3]);
     have to_integer(at(small_sum_b_3, b)) <= 1048323 by close() using { to_integer(b) <= 1048323; };
     have to_integer(at(small_sum_b_3, __rust_mir_133)) <= 458643 by close() using { to_integer(__rust_mir_133) <= 458643; };
     have to_integer(at(small_sum_b_3, b)) + to_integer(at(small_sum_b_3, __rust_mir_133)) <= 4294967295 by close() using { to_integer(at(small_sum_b_3, b)) <= 1048323; to_integer(at(small_sum_b_3, __rust_mir_133)) <= 458643; };
     step();
     have to_integer(at(small_sum_b_3, b) + at(small_sum_b_3, __rust_mir_133)) == to_integer(at(small_sum_b_3, b)) + to_integer(at(small_sum_b_3, __rust_mir_133)) by { apply(integer::uint32_add_to_integer(at(small_sum_b_3, b), at(small_sum_b_3, __rust_mir_133))); }
     have to_integer(__rust_mir_134) == to_integer(at(small_sum_b_3, b) + at(small_sum_b_3, __rust_mir_133));
     have __rust_mir_134 == at(small_sum_b_3, b) + at(small_sum_b_3, __rust_mir_133) by close() using { to_integer(__rust_mir_134) == to_integer(at(small_sum_b_3, b) + at(small_sum_b_3, __rust_mir_133)); to_integer(at(small_sum_b_3, b) + at(small_sum_b_3, __rust_mir_133)) == to_integer(at(small_sum_b_3, b)) + to_integer(at(small_sum_b_3, __rust_mir_133)); };
     have to_integer(__rust_mir_134) <= 1506966 by { rewrite(__rust_mir_134, at(small_sum_b_3, b) + at(small_sum_b_3, __rust_mir_133)); close() using { to_integer(at(small_sum_b_3, b)) <= 1048323; to_integer(at(small_sum_b_3, __rust_mir_133)) <= 458643; }; }
     step_until(assignment(b, 5).entry); step();
     have to_integer(b) <= 1506966 by close() using { to_integer(__rust_mir_134) <= 1506966; };
     have to_integer(__rust_mir_134) == to_integer(at(small_sum_b_3, b)) + to_integer(at(small_sum_b_3, __rust_mir_133)) by close() using { __rust_mir_134 == at(small_sum_b_3, b) + at(small_sum_b_3, __rust_mir_133); to_integer(at(small_sum_b_3, b) + at(small_sum_b_3, __rust_mir_133)) == to_integer(at(small_sum_b_3, b)) + to_integer(at(small_sum_b_3, __rust_mir_133)); };
     have to_integer(b) == to_integer(__rust_mir_134);
     have to_integer(b) == to_integer(at(weighted_b, b)) + to_integer(b_vec.0[0]) + to_integer(b_vec.0[1]) + to_integer(b_vec.0[2]) + to_integer(b_vec.0[3]) by close() using { to_integer(b) == to_integer(__rust_mir_134); to_integer(__rust_mir_134) == to_integer(at(small_sum_b_3, b)) + to_integer(at(small_sum_b_3, __rust_mir_133)); to_integer(at(small_sum_b_3, b)) == to_integer(at(weighted_b, b)) + to_integer(b_vec.0[0]) + to_integer(b_vec.0[1]) + to_integer(b_vec.0[2]); to_integer(at(small_sum_b_3, __rust_mir_133)) == to_integer(b_vec.0[3]); };

     step(); step(); step(); step(); step(); step(); step(); step();
     have remainder_len == bytes.len() % 4u64 by close();
     apply(adler_small_tail_metadata(bytes.len()));
     have remainder_len <= 3u64 by { rewrite(remainder_len, bytes.len() % 4u64); close(); }
     have remainder_len <= 2147483647u64 by normalize() using { remainder_len <= 3u64; };
     have to_integer(b) == adler_lane_b(to_integer(at(weighted_b, b)), to_integer(at(weighted_b, a_vec.0[1])), to_integer(at(weighted_b, a_vec.0[2])), to_integer(at(weighted_b, a_vec.0[3])), to_integer(at(weighted_b, b_vec.0[0])), to_integer(at(weighted_b, b_vec.0[1])), to_integer(at(weighted_b, b_vec.0[2])), to_integer(at(weighted_b, b_vec.0[3]))) by { unfold(adler_lane_b(to_integer(at(weighted_b, b)), to_integer(at(weighted_b, a_vec.0[1])), to_integer(at(weighted_b, a_vec.0[2])), to_integer(at(weighted_b, a_vec.0[3])), to_integer(at(weighted_b, b_vec.0[0])), to_integer(at(weighted_b, b_vec.0[1])), to_integer(at(weighted_b, b_vec.0[2])), to_integer(at(weighted_b, b_vec.0[3])))); close() using { to_integer(b) == to_integer(at(weighted_b, b)) + to_integer(b_vec.0[0]) + to_integer(b_vec.0[1]) + to_integer(b_vec.0[2]) + to_integer(b_vec.0[3]); to_integer(b_vec.0[0]) == to_integer(at(weighted_b, b_vec.0[0])) * 4; to_integer(b_vec.0[1]) == to_integer(at(weighted_b, b_vec.0[1])) * 4 + (65521 - to_integer(at(weighted_b, a_vec.0[1]))) * 1; to_integer(b_vec.0[2]) == to_integer(at(weighted_b, b_vec.0[2])) * 4 + (65521 - to_integer(at(weighted_b, a_vec.0[2]))) * 2; to_integer(b_vec.0[3]) == to_integer(at(weighted_b, b_vec.0[3])) * 4 + (65521 - to_integer(at(weighted_b, a_vec.0[3]))) * 3; }; }
     have truncating_remainder(to_integer(b), 65521) == adler_spec_b(bytes, (((bytes.len() - bytes.len() % 4u64) as u32) as i32), to_integer(at(vector_prefix, a)), to_integer(at(vector_prefix, b))) by { rewrite(to_integer(b), adler_lane_b(to_integer(at(weighted_b, b)), to_integer(at(weighted_b, a_vec.0[1])), to_integer(at(weighted_b, a_vec.0[2])), to_integer(at(weighted_b, a_vec.0[3])), to_integer(at(weighted_b, b_vec.0[0])), to_integer(at(weighted_b, b_vec.0[1])), to_integer(at(weighted_b, b_vec.0[2])), to_integer(at(weighted_b, b_vec.0[3])))); close(); }
     step_until(loop(5).entry);
     have to_integer(bytes.len() - bytes.len() % 4u64) <= to_integer(bytes.len()) by close() using { bytes.len() - bytes.len() % 4u64 <= bytes.len(); to_integer(bytes.len() - bytes.len() % 4u64) == to_integer(bytes.len()) - to_integer(bytes.len() % 4u64); };
     apply(adler_small_prefix_within_full(bytes.len()));
     apply(adler_small_signed_tail(bytes.len()));
     apply(adler_small_tail_indices(bytes.len()));
     have ((remainder_len as u32) as i32) == (((bytes.len() % 4u64) as u32) as i32) by { rewrite(remainder_len, bytes.len() % 4u64); normalize() using {}; }
     have 0 <= ((remainder_len as u32) as i32) by { rewrite(((remainder_len as u32) as i32), (((bytes.len() % 4u64) as u32) as i32)); close(); }
     have ((remainder_len as u32) as i32) <= 3 by { rewrite(((remainder_len as u32) as i32), (((bytes.len() % 4u64) as u32) as i32)); close(); }
     have ((remainder_len as u32) as i32) <= ((bytes.len() as u32) as i32) by { rewrite(((remainder_len as u32) as i32), (((bytes.len() % 4u64) as u32) as i32)); close(); }
     have ((bytes.len() as u32) as i32) - ((remainder_len as u32) as i32) == (((bytes.len() - bytes.len() % 4u64) as u32) as i32) by { rewrite(((remainder_len as u32) as i32), (((bytes.len() % 4u64) as u32) as i32)); have 0 <= (((bytes.len() % 4u64) as u32) as i32) by close(); have 0 <= ((bytes.len() as u32) as i32) by close(); have ((bytes.len() as u32) as i32) <= 22207 by close(); have to_integer(((bytes.len() as u32) as i32) - (((bytes.len() % 4u64) as u32) as i32)) == to_integer(((bytes.len() as u32) as i32)) - to_integer((((bytes.len() % 4u64) as u32) as i32)) by close() using { 0 <= (((bytes.len() % 4u64) as u32) as i32); (((bytes.len() % 4u64) as u32) as i32) <= ((bytes.len() as u32) as i32); 0 <= ((bytes.len() as u32) as i32); ((bytes.len() as u32) as i32) <= 22207; }; close() using { to_integer(((bytes.len() as u32) as i32) - (((bytes.len() % 4u64) as u32) as i32)) == to_integer(((bytes.len() as u32) as i32)) - to_integer((((bytes.len() % 4u64) as u32) as i32)); to_integer(((bytes.len() as u32) as i32) - (((bytes.len() % 4u64) as u32) as i32)) == to_integer((((bytes.len() - bytes.len() % 4u64) as u32) as i32)); }; }
      have __rust_mir_138_remaining == remainder_len;
      have ((__rust_mir_138_remaining as u32) as i32) == ((remainder_len as u32) as i32) by { rewrite(__rust_mir_138_remaining, remainder_len); normalize(); }
      have remainder_len <= 3u64 by { rewrite(remainder_len, bytes.len() % 4u64); close(); }
      have remainder_len <= bytes.len() by { rewrite(remainder_len, bytes.len() % 4u64); normalize(); }
      have __rust_mir_138_remaining <= remainder_len by { rewrite(__rust_mir_138_remaining, remainder_len); normalize(); }
     have 0 <= ((__rust_mir_138_remaining as u32) as i32) and ((__rust_mir_138_remaining as u32) as i32) <= ((remainder_len as u32) as i32) by { rewrite(((__rust_mir_138_remaining as u32) as i32), ((remainder_len as u32) as i32)); all { 0 <= ((remainder_len as u32) as i32) => { close(); } ((remainder_len as u32) as i32) <= ((remainder_len as u32) as i32) => { normalize() using {}; } } }
      have __rust_mir_138_base == remainder by normalize();
      have __rust_mir_138_length == remainder_len;
      have remainder == bytes + (bytes.len() - bytes.len() % 4u64) by normalize();
      have bytes.len() - __rust_mir_138_remaining == bytes.len() - bytes.len() % 4u64 by { rewrite(__rust_mir_138_remaining, remainder_len); rewrite(remainder_len, bytes.len() % 4u64); normalize(); }
      have __rust_mir_138_base == bytes + (bytes.len() - bytes.len() % 4u64) by { rewrite(__rust_mir_138_base, remainder); close(); }
     have adler_tail_consumed(((remainder_len as u32) as i32), ((__rust_mir_138_remaining as u32) as i32)) == 0 by { unfold(adler_tail_consumed(((remainder_len as u32) as i32), ((__rust_mir_138_remaining as u32) as i32))); rewrite(((__rust_mir_138_remaining as u32) as i32), ((remainder_len as u32) as i32)); close() using {}; }
     have adler_tail_a_ceiling(0) == 327600 by { unfold(adler_tail_a_ceiling(0)); normalize() using {}; }
     have adler_tail_b_ceiling(0) == 1506966 by { unfold(adler_tail_b_ceiling(0)); normalize() using {}; }
     have 0 <= to_integer(a);
     have to_integer(a) <= 4294967295;
     have 0 <= to_integer(b);
     have to_integer(b) <= 4294967295;
     have to_integer(a) <= adler_tail_a_ceiling(adler_tail_consumed(((remainder_len as u32) as i32), ((__rust_mir_138_remaining as u32) as i32))) by { rewrite(adler_tail_consumed(((remainder_len as u32) as i32), ((__rust_mir_138_remaining as u32) as i32)), 0); rewrite(adler_tail_a_ceiling(0), 327600); close(); }
     have to_integer(b) <= adler_tail_b_ceiling(adler_tail_consumed(((remainder_len as u32) as i32), ((__rust_mir_138_remaining as u32) as i32))) by { rewrite(adler_tail_consumed(((remainder_len as u32) as i32), ((__rust_mir_138_remaining as u32) as i32)), 0); rewrite(adler_tail_b_ceiling(0), 1506966); close(); }
     have old(to_integer((self.a as u32))) == to_integer(at(vector_prefix, a));
     have old(to_integer((self.b as u32))) == to_integer(at(vector_prefix, b));
     have 0 <= to_integer((old((self.a as u32))));
     have to_integer((old((self.a as u32)))) <= 4294967295;
     have to_integer((old((self.a as u32)))) <= to_integer(65520u32);
     have ((__rust_mir_138_remaining as u32) as i32) <= ((bytes.len() as u32) as i32) by close() using { ((__rust_mir_138_remaining as u32) as i32) == ((remainder_len as u32) as i32); ((remainder_len as u32) as i32) <= ((bytes.len() as u32) as i32); };
     have defined((((bytes.len() as u32) as i32)) - (((__rust_mir_138_remaining as u32) as i32)));
     have (((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)) == (((bytes.len() - bytes.len() % 4u64) as u32) as i32) by { rewrite(((__rust_mir_138_remaining as u32) as i32), ((remainder_len as u32) as i32)); close(); }
     have 0 <= old(to_integer((self.a as u32))) by close();
     have old(to_integer((self.a as u32))) <= 65520 by close();
     have 0 <= to_integer((at(vector_prefix, b)));
     have to_integer((at(vector_prefix, b))) <= 4294967295;
     have truncating_remainder(to_integer(a), 65521) == adler_spec_a(bytes, (((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)), old(to_integer((self.a as u32)))) by { rewrite((((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)), (((bytes.len() - bytes.len() % 4u64) as u32) as i32)); rewrite(old(to_integer((self.a as u32))), to_integer(at(vector_prefix, a))); close(); }
     have truncating_remainder(to_integer(b), 65521) == adler_spec_b(bytes, (((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)), old(to_integer((self.a as u32))), old(to_integer((self.b as u32)))) by { rewrite((((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)), (((bytes.len() - bytes.len() % 4u64) as u32) as i32)); rewrite(old(to_integer((self.a as u32))), to_integer(at(vector_prefix, a))); rewrite(old(to_integer((self.b as u32))), to_integer(at(vector_prefix, b))); close(); }
     loop {
      decreases __rust_mir_138_remaining;
      views *bytes;
      invariant bytes.len() <= 22207u64;
      invariant bytes.len() == old(bytes.len());
      invariant bytes == old(bytes);
      invariant forall (k: int32) { 0 <= k and k < ((bytes.len() as u32) as i32) implies bytes[k] == old(bytes[k]) };
      invariant 0 <= ((remainder_len as u32) as i32) and ((remainder_len as u32) as i32) <= 3;
      invariant ((remainder_len as u32) as i32) <= ((bytes.len() as u32) as i32);
      invariant 0 <= ((bytes.len() as u32) as i32) and ((bytes.len() as u32) as i32) <= 22207;
      invariant 0 <= ((__rust_mir_138_remaining as u32) as i32) and ((__rust_mir_138_remaining as u32) as i32) <= ((remainder_len as u32) as i32);
       invariant remainder_len <= 3u64;
       invariant remainder_len <= bytes.len();
       invariant __rust_mir_138_remaining <= remainder_len;
       invariant __rust_mir_138_base == bytes + (bytes.len() - bytes.len() % 4u64);
       invariant __rust_mir_138_length == remainder_len;
      invariant defined((((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)));
      invariant 0 <= old(to_integer((self.a as u32))) and old(to_integer((self.a as u32))) <= 65520;
      invariant 0 <= old(to_integer((self.b as u32)));
      invariant truncating_remainder(to_integer(a), 65521) == adler_spec_a(bytes, (((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)), old(to_integer((self.a as u32))));
      invariant truncating_remainder(to_integer(b), 65521) == adler_spec_b(bytes, (((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)), old(to_integer((self.a as u32))), old(to_integer((self.b as u32))));
      invariant 0 <= to_integer(a) and to_integer(a) <= adler_tail_a_ceiling(adler_tail_consumed(((remainder_len as u32) as i32), ((__rust_mir_138_remaining as u32) as i32)));
      invariant 0 <= to_integer(b) and to_integer(b) <= adler_tail_b_ceiling(adler_tail_consumed(((remainder_len as u32) as i32), ((__rust_mir_138_remaining as u32) as i32)));
      maintain by {
        have 0u64 < __rust_mir_138_remaining;
        have 1u64 <= __rust_mir_138_remaining by close() using { 0u64 < __rust_mir_138_remaining; };
        have __rust_mir_138_remaining <= 22208u64 by close() using { __rust_mir_138_remaining <= remainder_len; remainder_len <= 3u64; };
        apply(adler_count_tail_step(__rust_mir_138_remaining));
        have 0 < ((__rust_mir_138_remaining as u32) as i32) by close() using { 1 <= ((__rust_mir_138_remaining as u32) as i32); };
       have 1 <= ((__rust_mir_138_remaining as u32) as i32) by close() using { 0 < ((__rust_mir_138_remaining as u32) as i32); };
       have 0 <= ((__rust_mir_138_remaining as u32) as i32) - 1 by close() using { 0 < ((__rust_mir_138_remaining as u32) as i32); };
       have (((__rust_mir_138_remaining as u32) as i32)) - 1 <= (((remainder_len as u32) as i32));
       mark tail_head;
       have 1 <= at(tail_head, ((__rust_mir_138_remaining as u32) as i32));
       have at(tail_head, ((__rust_mir_138_remaining as u32) as i32)) <= ((remainder_len as u32) as i32);
       have at(tail_head, ((__rust_mir_138_remaining as u32) as i32)) <= ((bytes.len() as u32) as i32) by close() using { at(tail_head, ((__rust_mir_138_remaining as u32) as i32)) <= ((remainder_len as u32) as i32); ((remainder_len as u32) as i32) <= ((bytes.len() as u32) as i32); };
       have to_integer(a) <= adler_tail_a_ceiling(adler_tail_consumed(((remainder_len as u32) as i32), at(tail_head, ((__rust_mir_138_remaining as u32) as i32))));
       have to_integer(b) <= adler_tail_b_ceiling(adler_tail_consumed(((remainder_len as u32) as i32), at(tail_head, ((__rust_mir_138_remaining as u32) as i32))));
        have 1u64 <= at(tail_head, __rust_mir_138_remaining);
        have at(tail_head, __rust_mir_138_remaining) <= remainder_len;
        have bytes.len() - at(tail_head, __rust_mir_138_remaining) < bytes.len() by close() using { 1u64 <= at(tail_head, __rust_mir_138_remaining); at(tail_head, __rust_mir_138_remaining) <= remainder_len; remainder_len <= bytes.len(); };
       have truncating_remainder(to_integer(at(tail_head, a)), 65521) == adler_spec_a(bytes, (((bytes.len() as u32) as i32) - at(tail_head, ((__rust_mir_138_remaining as u32) as i32))), old(to_integer((self.a as u32))));
       have truncating_remainder(to_integer(at(tail_head, b)), 65521) == adler_spec_b(bytes, (((bytes.len() as u32) as i32) - at(tail_head, ((__rust_mir_138_remaining as u32) as i32))), old(to_integer((self.a as u32))), old(to_integer((self.b as u32))));
       apply(adler_tail_read_offset(bytes.len() - bytes.len() % 4u64, bytes.len(), remainder_len, __rust_mir_138_remaining));
       have at(tail_head, loop(5).iter.as_slice()) == __rust_mir_138_base + (__rust_mir_138_length - at(tail_head, __rust_mir_138_remaining));
        have to_integer(at(tail_head, __rust_mir_138_remaining)) <= to_integer(bytes.len() - (bytes.len() - bytes.len() % 4u64));
        apply(adler_tail_pointer_position(bytes, bytes.len() - bytes.len() % 4u64, bytes.len(), at(tail_head, __rust_mir_138_remaining)));
        have at(tail_head, loop(5).iter.as_slice()) == bytes + (bytes.len() - at(tail_head, __rust_mir_138_remaining)) by close() using { at(tail_head, loop(5).iter.as_slice()) == __rust_mir_138_base + (__rust_mir_138_length - at(tail_head, __rust_mir_138_remaining)); __rust_mir_138_base == bytes + (bytes.len() - bytes.len() % 4u64); __rust_mir_138_length == remainder_len; to_integer(remainder_len) == to_integer(bytes.len() - (bytes.len() - bytes.len() % 4u64)); (bytes + (bytes.len() - bytes.len() % 4u64)) + ((bytes.len() - (bytes.len() - bytes.len() % 4u64)) - at(tail_head, __rust_mir_138_remaining)) == bytes + (bytes.len() - at(tail_head, __rust_mir_138_remaining)); };
       step_until(loop(5).statement(0).entry);
       have __rust_mir_138_remaining == at(tail_head, __rust_mir_138_remaining) - 1u64;
       have at(tail_head, __rust_mir_138_remaining) <= 2147483647u64 by close() using { at(tail_head, __rust_mir_138_remaining) <= remainder_len; remainder_len <= 3u64; };
       have __rust_mir_138_remaining <= 2147483647u64 by close() using { __rust_mir_138_remaining == at(tail_head, __rust_mir_138_remaining) - 1u64; 1u64 <= at(tail_head, __rust_mir_138_remaining); at(tail_head, __rust_mir_138_remaining) <= 2147483647u64; };
       apply(adler_index_observation(at(tail_head, __rust_mir_138_remaining)));
       apply(adler_index_observation(__rust_mir_138_remaining));
       have ((__rust_mir_138_remaining as u32) as i32) == at(tail_head, ((__rust_mir_138_remaining as u32) as i32)) - 1 by close() using { to_integer(__rust_mir_138_remaining as uint32 as int32) == to_integer(__rust_mir_138_remaining); to_integer(at(tail_head, __rust_mir_138_remaining) as uint32 as int32) == to_integer(at(tail_head, __rust_mir_138_remaining)); __rust_mir_138_remaining == at(tail_head, __rust_mir_138_remaining) - 1u64; };
       have __rust_mir_138_remaining <= bytes.len() by close() using { __rust_mir_138_remaining == at(tail_head, __rust_mir_138_remaining) - 1u64; 1u64 <= at(tail_head, __rust_mir_138_remaining); at(tail_head, __rust_mir_138_remaining) <= remainder_len; remainder_len <= bytes.len(); };
       have 1u64 <= bytes.len() - __rust_mir_138_remaining by close() using { __rust_mir_138_remaining == at(tail_head, __rust_mir_138_remaining) - 1u64; 1u64 <= at(tail_head, __rust_mir_138_remaining); at(tail_head, __rust_mir_138_remaining) <= remainder_len; remainder_len <= bytes.len(); };
       have 0 <= ((__rust_mir_138_remaining as u32) as i32) by close() using { ((__rust_mir_138_remaining as u32) as i32) == at(tail_head, ((__rust_mir_138_remaining as u32) as i32)) - 1; 1 <= at(tail_head, ((__rust_mir_138_remaining as u32) as i32)); at(tail_head, ((__rust_mir_138_remaining as u32) as i32)) <= ((bytes.len() as u32) as i32); };
       have at(tail_head, ((__rust_mir_138_remaining as u32) as i32)) - 1 <= ((bytes.len() as u32) as i32) by close() using { 1 <= at(tail_head, ((__rust_mir_138_remaining as u32) as i32)); at(tail_head, ((__rust_mir_138_remaining as u32) as i32)) <= ((bytes.len() as u32) as i32); };
       have ((__rust_mir_138_remaining as u32) as i32) <= ((bytes.len() as u32) as i32) by { rewrite(((__rust_mir_138_remaining as u32) as i32), at(tail_head, ((__rust_mir_138_remaining as u32) as i32)) - 1); close(); }
       have defined((((bytes.len() as u32) as i32)) - (((__rust_mir_138_remaining as u32) as i32)));
       have 1 <= (((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)) by close() using { ((__rust_mir_138_remaining as u32) as i32) == at(tail_head, ((__rust_mir_138_remaining as u32) as i32)) - 1; 1 <= at(tail_head, ((__rust_mir_138_remaining as u32) as i32)); at(tail_head, ((__rust_mir_138_remaining as u32) as i32)) <= ((bytes.len() as u32) as i32); ((bytes.len() as u32) as i32) <= 22207; };
       apply(integer::int32_subtract_to_integer(((bytes.len() as u32) as i32), ((__rust_mir_138_remaining as u32) as i32)));
       have to_integer(((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)) - 1 <= 2147483647 by close() using { to_integer(((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)) == to_integer(((bytes.len() as u32) as i32)) - to_integer(((__rust_mir_138_remaining as u32) as i32)); ((bytes.len() as u32) as i32) <= 22207; 0 <= ((__rust_mir_138_remaining as u32) as i32); };
       have to_integer(((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)) - 1 >= -2147483648 by close() using { to_integer(((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)) == to_integer(((bytes.len() as u32) as i32)) - to_integer(((__rust_mir_138_remaining as u32) as i32)); 1 <= (((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)); };
       have defined(((((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32))) - 1);
       have to_integer(((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)) - 1 <= 2147483647 and to_integer(((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)) - 1 >= -2147483648 by { all { to_integer(((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)) - 1 <= 2147483647 => { close(); } to_integer(((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)) - 1 >= -2147483648 => { close(); } } }
       apply(integer::int32_subtract_to_integer((((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)), 1));
       have 0 <= to_integer(((((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)) - 1)) by close() using { to_integer(((((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)) - 1)) == to_integer(((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)) - 1; to_integer(((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)) == to_integer(((bytes.len() as u32) as i32)) - to_integer(((__rust_mir_138_remaining as u32) as i32)); 1 <= (((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)); };
       have to_integer(((((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)) - 1)) <= 2147483646 by close() using { to_integer(((((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)) - 1)) == to_integer(((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)) - 1; to_integer(((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)) == to_integer(((bytes.len() as u32) as i32)) - to_integer(((__rust_mir_138_remaining as u32) as i32)); 0 <= ((__rust_mir_138_remaining as u32) as i32); ((bytes.len() as u32) as i32) <= 22207; };
       have ((((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)) - 1) == (((bytes.len() as u32) as i32) - at(tail_head, ((__rust_mir_138_remaining as u32) as i32))) by close() using { ((__rust_mir_138_remaining as u32) as i32) == at(tail_head, ((__rust_mir_138_remaining as u32) as i32)) - 1; 1 <= at(tail_head, ((__rust_mir_138_remaining as u32) as i32)); at(tail_head, ((__rust_mir_138_remaining as u32) as i32)) <= ((bytes.len() as u32) as i32); ((bytes.len() as u32) as i32) <= 22207; };
       have 0 <= ((((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)) - 1) by close() using { ((((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)) - 1) == (((bytes.len() as u32) as i32) - at(tail_head, ((__rust_mir_138_remaining as u32) as i32))); 1 <= at(tail_head, ((__rust_mir_138_remaining as u32) as i32)); at(tail_head, ((__rust_mir_138_remaining as u32) as i32)) <= ((bytes.len() as u32) as i32); ((bytes.len() as u32) as i32) <= 22207; };
       have ((((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)) - 1) <= 2147483646 by close() using { ((((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)) - 1) == (((bytes.len() as u32) as i32) - at(tail_head, ((__rust_mir_138_remaining as u32) as i32))); 1 <= at(tail_head, ((__rust_mir_138_remaining as u32) as i32)); at(tail_head, ((__rust_mir_138_remaining as u32) as i32)) <= ((bytes.len() as u32) as i32); ((bytes.len() as u32) as i32) <= 22207; };
       have (((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)) == ((((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)) - 1) + 1 by close() using { 0 <= to_integer(((((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)) - 1)); to_integer(((((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)) - 1)) <= 2147483646; ((((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)) - 1) == (((bytes.len() as u32) as i32) - at(tail_head, ((__rust_mir_138_remaining as u32) as i32))); ((__rust_mir_138_remaining as u32) as i32) == at(tail_head, ((__rust_mir_138_remaining as u32) as i32)) - 1; 1 <= at(tail_head, ((__rust_mir_138_remaining as u32) as i32)); at(tail_head, ((__rust_mir_138_remaining as u32) as i32)) <= ((bytes.len() as u32) as i32); ((bytes.len() as u32) as i32) <= 22207; };
       have bytes.len() - __rust_mir_138_remaining - 1u64 == bytes.len() - at(tail_head, __rust_mir_138_remaining) by close() using { __rust_mir_138_remaining == at(tail_head, __rust_mir_138_remaining) - 1u64; 1u64 <= at(tail_head, __rust_mir_138_remaining); at(tail_head, __rust_mir_138_remaining) <= remainder_len; remainder_len <= bytes.len(); };
       apply(integer::uint64_subtract_to_integer(bytes.len(), __rust_mir_138_remaining));
       have at(tail_head, __rust_mir_138_remaining) <= bytes.len() by close() using { at(tail_head, __rust_mir_138_remaining) <= remainder_len; remainder_len <= bytes.len(); };
       apply(integer::uint64_subtract_to_integer(bytes.len(), at(tail_head, __rust_mir_138_remaining)));
       have to_integer(1u64) <= to_integer(bytes.len() - __rust_mir_138_remaining) by close() using { to_integer(bytes.len() - __rust_mir_138_remaining) == to_integer(bytes.len()) - to_integer(__rust_mir_138_remaining); 1u64 <= bytes.len() - __rust_mir_138_remaining; };
       apply(integer::uint64_subtract_to_integer(bytes.len() - __rust_mir_138_remaining, 1u64));
       have to_integer(bytes.len() - __rust_mir_138_remaining - 1u64) == to_integer(bytes.len() - at(tail_head, __rust_mir_138_remaining)) by close() using { to_integer(bytes.len() - __rust_mir_138_remaining) == to_integer(bytes.len()) - to_integer(__rust_mir_138_remaining); to_integer(bytes.len() - at(tail_head, __rust_mir_138_remaining)) == to_integer(bytes.len()) - to_integer(at(tail_head, __rust_mir_138_remaining)); to_integer(bytes.len() - __rust_mir_138_remaining - 1u64) == to_integer(bytes.len() - __rust_mir_138_remaining) - to_integer(1u64); __rust_mir_138_remaining == at(tail_head, __rust_mir_138_remaining) - 1u64; };
       have at(tail_head, loop(5).iter.as_slice()) == bytes + (bytes.len() - __rust_mir_138_remaining - 1u64) by close() using { at(tail_head, loop(5).iter.as_slice()) == bytes + (bytes.len() - at(tail_head, __rust_mir_138_remaining)); to_integer(bytes.len() - __rust_mir_138_remaining - 1u64) == to_integer(bytes.len() - at(tail_head, __rust_mir_138_remaining)); };
       apply(adler_count_previous_byte_observation(bytes, bytes.len(), __rust_mir_138_remaining));
       have (byte as u32) == (at(tail_head, loop(5).iter.as_slice()[0]) as u32);
       apply(adler_helper_byte_observation(at(tail_head, loop(5).iter.as_slice()[0])));
       have to_integer(byte as u32) == to_integer(((bytes + (bytes.len() - __rust_mir_138_remaining - 1u64))[0] as i32)) by { rewrite((byte as u32), (at(tail_head, loop(5).iter.as_slice()[0]) as u32)); rewrite(to_integer((at(tail_head, loop(5).iter.as_slice()[0]) as u32)), to_integer((at(tail_head, loop(5).iter.as_slice()[0]) as i32))); rewrite(at(tail_head, loop(5).iter.as_slice()), bytes + (bytes.len() - __rust_mir_138_remaining - 1u64)); normalize(); }
       have to_integer(byte as u32) == to_integer((bytes[((((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)) - 1)] as i32)) by { rewrite(to_integer(byte as u32), to_integer(((bytes + (bytes.len() - __rust_mir_138_remaining - 1u64))[0] as i32))); close(); }
       have truncating_remainder(to_integer(a), 65521) == adler_spec_a(bytes, ((((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)) - 1), old(to_integer((self.a as u32)))) by { rewrite(((((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)) - 1), (((bytes.len() as u32) as i32) - at(tail_head, ((__rust_mir_138_remaining as u32) as i32)))); close(); }
       have truncating_remainder(to_integer(b), 65521) == adler_spec_b(bytes, ((((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)) - 1), old(to_integer((self.a as u32))), old(to_integer((self.b as u32)))) by { rewrite(((((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)) - 1), (((bytes.len() as u32) as i32) - at(tail_head, ((__rust_mir_138_remaining as u32) as i32)))); close(); }
       apply(adler_prefix_a_step_one(bytes, ((((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)) - 1), old(to_integer((self.a as u32))), to_integer(a)));
       apply(adler_prefix_b_step_one(bytes, ((((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)) - 1), old(to_integer((self.a as u32))), old(to_integer((self.b as u32))), to_integer(a), to_integer(b)));
       have (byte as u32) <= 255u32;
       have to_integer(byte as u32) <= to_integer(255u32);
       have to_integer(byte as u32) <= 255 by close() using { to_integer(byte as u32) <= to_integer(255u32); };
       apply(adler_tail_iterator_step(((remainder_len as u32) as i32), at(tail_head, ((__rust_mir_138_remaining as u32) as i32)), to_integer(a), to_integer(b), to_integer(byte as u32)));
       have a <= 4294967295u32 - (byte as u32);
       step_until(assignment(__rust_mir_146, 0).entry);
       mark tail_add_a;
       have to_integer(at(tail_add_a, a)) == to_integer(a) by normalize();
       have to_integer(at(tail_add_a, b)) == to_integer(b) by normalize();
       have to_integer(at(tail_add_a, byte as u32)) == to_integer((bytes[((((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)) - 1)] as i32)) by normalize() using { to_integer(byte as u32) == to_integer((bytes[((((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)) - 1)] as i32)); };
       have truncating_remainder(to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, byte as u32)), 65521) == adler_spec_a(bytes, (((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)), old(to_integer((self.a as u32)))) by {
        rewrite((((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)), ((((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)) - 1) + 1);
        rewrite(to_integer(at(tail_add_a, a)), to_integer(a));
        rewrite(to_integer(at(tail_add_a, byte as u32)), to_integer((bytes[((((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)) - 1)] as i32)));
        close();
       }
       have truncating_remainder(to_integer(at(tail_add_a, b)) + to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, byte as u32)), 65521) == adler_spec_b(bytes, (((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)), old(to_integer((self.a as u32))), old(to_integer((self.b as u32)))) by {
        rewrite((((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)), ((((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)) - 1) + 1);
        rewrite(to_integer(at(tail_add_a, b)), to_integer(b));
        rewrite(to_integer(at(tail_add_a, a)), to_integer(a));
        rewrite(to_integer(at(tail_add_a, byte as u32)), to_integer((bytes[((((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)) - 1)] as i32)));
        close();
       }

       have to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, byte as u32)) <= 4294967295;
       step();
       have to_integer(at(tail_add_a, a) + at(tail_add_a, byte as u32)) == to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, byte as u32)) by { apply(integer::uint32_add_to_integer(at(tail_add_a, a), at(tail_add_a, byte as u32))); }
       have to_integer(__rust_mir_146) == to_integer(at(tail_add_a, a) + at(tail_add_a, byte as u32));
       have __rust_mir_146 == at(tail_add_a, a) + at(tail_add_a, byte as u32) by close() using { to_integer(__rust_mir_146) == to_integer(at(tail_add_a, a) + at(tail_add_a, byte as u32)); to_integer(at(tail_add_a, a) + at(tail_add_a, byte as u32)) == to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, byte as u32)); };
       have to_integer(__rust_mir_146) == to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, byte as u32)) by { rewrite(__rust_mir_146, at(tail_add_a, a) + at(tail_add_a, byte as u32)); close(); }
       have to_integer(__rust_mir_146) <= adler_tail_a_ceiling(adler_tail_consumed(((remainder_len as u32) as i32), at(tail_head, ((__rust_mir_138_remaining as u32) as i32))) + 1) by close() using { to_integer(a) + to_integer(byte as u32) <= adler_tail_a_ceiling(adler_tail_consumed(((remainder_len as u32) as i32), at(tail_head, ((__rust_mir_138_remaining as u32) as i32))) + 1); to_integer(__rust_mir_146) == to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, byte as u32)); };
       have to_integer(b) + to_integer(__rust_mir_146) <= 4294967295 by close() using { to_integer(b) + to_integer(a) + to_integer(byte as u32) <= 4294967295; to_integer(__rust_mir_146) == to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, byte as u32)); };
       have to_integer(b) + to_integer(__rust_mir_146) <= adler_tail_b_ceiling(adler_tail_consumed(((remainder_len as u32) as i32), at(tail_head, ((__rust_mir_138_remaining as u32) as i32))) + 1) by close() using { to_integer(b) + to_integer(a) + to_integer(byte as u32) <= adler_tail_b_ceiling(adler_tail_consumed(((remainder_len as u32) as i32), at(tail_head, ((__rust_mir_138_remaining as u32) as i32))) + 1); to_integer(__rust_mir_146) == to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, byte as u32)); };
       step_until(assignment(a, 2).entry); step();
       have to_integer(a) <= adler_tail_a_ceiling(adler_tail_consumed(((remainder_len as u32) as i32), at(tail_head, ((__rust_mir_138_remaining as u32) as i32))) + 1);
       have a == __rust_mir_146;
       have to_integer(a) == to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, byte as u32)) by { rewrite(a, __rust_mir_146); close(); }
       have truncating_remainder(to_integer(a), 65521) == adler_spec_a(bytes, (((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)), old(to_integer((self.a as u32)))) by { rewrite(to_integer(a), to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, byte as u32))); close(); }
       step_until(assignment(__rust_mir_147, 0).entry); step();
       have __rust_mir_147 == a;
       have a == __rust_mir_146;
       have to_integer(b) + to_integer(__rust_mir_147) <= adler_tail_b_ceiling(adler_tail_consumed(((remainder_len as u32) as i32), at(tail_head, ((__rust_mir_138_remaining as u32) as i32))) + 1) by { rewrite(__rust_mir_147, a); rewrite(a, __rust_mir_146); close(); }
       have to_integer(b) + to_integer(__rust_mir_147) <= 4294967295;
       have b <= 4294967295u32 - __rust_mir_147 by close() using { to_integer(b) + to_integer(__rust_mir_147) <= 4294967295; };
       step_until(assignment(__rust_mir_148, 0).entry);
       mark tail_add_b;
       have to_integer(at(tail_add_b, b)) == to_integer(at(tail_add_a, b));
       have at(tail_add_b, __rust_mir_147) == __rust_mir_147 by normalize();
       have to_integer(at(tail_add_b, __rust_mir_147)) == to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, byte as u32)) by {
        rewrite(at(tail_add_b, __rust_mir_147), __rust_mir_147);
        rewrite(__rust_mir_147, a);
        close();
       }

       have to_integer(at(tail_add_b, b)) + to_integer(at(tail_add_b, __rust_mir_147)) <= adler_tail_b_ceiling(adler_tail_consumed(((remainder_len as u32) as i32), at(tail_head, ((__rust_mir_138_remaining as u32) as i32))) + 1) by close() using { to_integer(b) + to_integer(__rust_mir_147) <= adler_tail_b_ceiling(adler_tail_consumed(((remainder_len as u32) as i32), at(tail_head, ((__rust_mir_138_remaining as u32) as i32))) + 1); };
       have to_integer(at(tail_add_b, b)) + to_integer(at(tail_add_b, __rust_mir_147)) <= 4294967295;
       step();
       have to_integer(__rust_mir_148) == to_integer(at(tail_add_b, b) + at(tail_add_b, __rust_mir_147));
       have to_integer(at(tail_add_b, b) + at(tail_add_b, __rust_mir_147)) == to_integer(at(tail_add_b, b)) + to_integer(at(tail_add_b, __rust_mir_147));

       have to_integer(__rust_mir_148) == to_integer(at(tail_add_b, b)) + to_integer(at(tail_add_b, __rust_mir_147)) by { rewrite(to_integer(__rust_mir_148), to_integer(at(tail_add_b, b) + at(tail_add_b, __rust_mir_147))); close(); }
       have to_integer(__rust_mir_148) <= adler_tail_b_ceiling(adler_tail_consumed(((remainder_len as u32) as i32), at(tail_head, ((__rust_mir_138_remaining as u32) as i32))) + 1) by { rewrite(to_integer(__rust_mir_148), to_integer(at(tail_add_b, b)) + to_integer(at(tail_add_b, __rust_mir_147))); close(); }
       step_until(assignment(b, 6).entry); step();
       have to_integer(b) <= adler_tail_b_ceiling(adler_tail_consumed(((remainder_len as u32) as i32), at(tail_head, ((__rust_mir_138_remaining as u32) as i32))) + 1);
       have to_integer(b) == to_integer(at(tail_add_a, b)) + to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, byte as u32)) by close() using { to_integer(__rust_mir_148) == to_integer(at(tail_add_b, b)) + to_integer(at(tail_add_b, __rust_mir_147)); to_integer(at(tail_add_b, b)) == to_integer(at(tail_add_a, b)); to_integer(at(tail_add_b, __rust_mir_147)) == to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, byte as u32)); };
       have truncating_remainder(to_integer(b), 65521) == adler_spec_b(bytes, (((bytes.len() as u32) as i32) - ((__rust_mir_138_remaining as u32) as i32)), old(to_integer((self.a as u32))), old(to_integer((self.b as u32)))) by { rewrite(to_integer(b), to_integer(at(tail_add_a, b)) + to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, byte as u32))); close(); }
       step_until(loop.back_edge);
        have to_integer(__rust_mir_138_remaining) == to_integer(at(tail_head, __rust_mir_138_remaining) - 1u64);
        have to_integer(((__rust_mir_138_remaining as u32) as i32)) == to_integer(at(tail_head, ((__rust_mir_138_remaining as u32) as i32)) - 1) by { rewrite(to_integer(__rust_mir_138_remaining), to_integer(at(tail_head, __rust_mir_138_remaining) - 1u64)); close(); }
       apply(adler_tail_remaining_progress(((remainder_len as u32) as i32), at(tail_head, ((__rust_mir_138_remaining as u32) as i32))));
       have adler_tail_consumed(((remainder_len as u32) as i32), ((__rust_mir_138_remaining as u32) as i32)) == adler_tail_consumed(((remainder_len as u32) as i32), at(tail_head, ((__rust_mir_138_remaining as u32) as i32))) + 1 by { rewrite(to_integer(((__rust_mir_138_remaining as u32) as i32)), to_integer(at(tail_head, ((__rust_mir_138_remaining as u32) as i32)) - 1)); close(); }
       have to_integer(a) <= adler_tail_a_ceiling(adler_tail_consumed(((remainder_len as u32) as i32), ((__rust_mir_138_remaining as u32) as i32))) by { rewrite(adler_tail_consumed(((remainder_len as u32) as i32), ((__rust_mir_138_remaining as u32) as i32)), adler_tail_consumed(((remainder_len as u32) as i32), at(tail_head, ((__rust_mir_138_remaining as u32) as i32))) + 1); close(); }
       have to_integer(b) <= adler_tail_b_ceiling(adler_tail_consumed(((remainder_len as u32) as i32), ((__rust_mir_138_remaining as u32) as i32))) by { rewrite(adler_tail_consumed(((remainder_len as u32) as i32), ((__rust_mir_138_remaining as u32) as i32)), adler_tail_consumed(((remainder_len as u32) as i32), at(tail_head, ((__rust_mir_138_remaining as u32) as i32))) + 1); close(); }
       have 0 <= to_integer(a); have to_integer(a) <= 4294967295; have 0 <= to_integer(b); have to_integer(b) <= 4294967295; 
       have 0 <= ((__rust_mir_138_remaining as u32) as i32) and ((__rust_mir_138_remaining as u32) as i32) <= ((remainder_len as u32) as i32);
        have __rust_mir_138_remaining <= remainder_len by close() using { to_integer(__rust_mir_138_remaining) == to_integer(at(tail_head, __rust_mir_138_remaining) - 1u64); 1u64 <= at(tail_head, __rust_mir_138_remaining); at(tail_head, __rust_mir_138_remaining) <= remainder_len; };
        have to_integer(bytes.len() - at(tail_head, __rust_mir_138_remaining)) <= to_integer(18446744073709551614u64) by close() using { 1u64 <= at(tail_head, __rust_mir_138_remaining); at(tail_head, __rust_mir_138_remaining) <= remainder_len; remainder_len <= bytes.len(); };
        have to_integer(bytes.len() - __rust_mir_138_remaining) == to_integer((bytes.len() - at(tail_head, __rust_mir_138_remaining)) + 1u64) by close() using { to_integer(__rust_mir_138_remaining) == to_integer(at(tail_head, __rust_mir_138_remaining) - 1u64); 1u64 <= at(tail_head, __rust_mir_138_remaining); at(tail_head, __rust_mir_138_remaining) <= remainder_len; remainder_len <= bytes.len(); };
        have __rust_mir_138_remaining < at(tail_head, __rust_mir_138_remaining) by close() using { to_integer(__rust_mir_138_remaining) == to_integer(at(tail_head, __rust_mir_138_remaining) - 1u64); 1u64 <= at(tail_head, __rust_mir_138_remaining); };
       have defined((((bytes.len() as u32) as i32)) - (((__rust_mir_138_remaining as u32) as i32)));
      }
     }

     step_until(statement(22).entry);
     have at(loop(5).exit, __rust_mir_138_remaining) == 0u64 by close() using { not (0u64 < at(loop(5).exit, __rust_mir_138_remaining)); };
     have at(loop(5).exit, ((__rust_mir_138_remaining as u32) as i32)) == 0 by { rewrite(at(loop(5).exit, __rust_mir_138_remaining), 0u64); normalize(); }
     have truncating_remainder(to_integer(at(loop(5).exit, a)), 65521) == adler_spec_a(bytes, (((bytes.len() as u32) as i32) - at(loop(5).exit, ((__rust_mir_138_remaining as u32) as i32))), old(to_integer((self.a as u32)))) by close();
     have to_integer(a) == to_integer(at(loop(5).exit, a)) by normalize();
     have to_integer(((bytes.len() as u32) as i32)) == to_integer((((bytes.len() as u32) as i32) - at(loop(5).exit, ((__rust_mir_138_remaining as u32) as i32)))) by { rewrite(at(loop(5).exit, ((__rust_mir_138_remaining as u32) as i32)), 0); normalize(); }
     have truncating_remainder(to_integer(a), 65521) == adler_spec_a(bytes, ((bytes.len() as u32) as i32), old(to_integer((self.a as u32)))) by { rewrite(to_integer(a), to_integer(at(loop(5).exit, a))); rewrite(to_integer(((bytes.len() as u32) as i32)), to_integer((((bytes.len() as u32) as i32) - at(loop(5).exit, ((__rust_mir_138_remaining as u32) as i32))))); close(); }
     have truncating_remainder(to_integer(at(loop(5).exit, b)), 65521) == adler_spec_b(bytes, (((bytes.len() as u32) as i32) - at(loop(5).exit, ((__rust_mir_138_remaining as u32) as i32))), old(to_integer((self.a as u32))), old(to_integer((self.b as u32)))) by close();
     have to_integer(b) == to_integer(at(loop(5).exit, b)) by normalize();
     have to_integer(((bytes.len() as u32) as i32)) == to_integer((((bytes.len() as u32) as i32) - at(loop(5).exit, ((__rust_mir_138_remaining as u32) as i32)))) by { rewrite(at(loop(5).exit, ((__rust_mir_138_remaining as u32) as i32)), 0); normalize(); }
     have truncating_remainder(to_integer(b), 65521) == adler_spec_b(bytes, ((bytes.len() as u32) as i32), old(to_integer((self.a as u32))), old(to_integer((self.b as u32)))) by { rewrite(to_integer(b), to_integer(at(loop(5).exit, b))); rewrite(to_integer(((bytes.len() as u32) as i32)), to_integer((((bytes.len() as u32) as i32) - at(loop(5).exit, ((__rust_mir_138_remaining as u32) as i32))))); close(); }
     have forall (k: int32) { 0 <= k and k < ((bytes.len() as u32) as i32) implies bytes[k] == old(bytes[k]) } by close();
     apply(adler_spec_extensional(bytes, old(bytes), ((bytes.len() as u32) as i32), old(to_integer((self.a as u32))), old(to_integer((self.b as u32)))));
     have adler_spec_a(bytes, ((bytes.len() as u32) as i32), old(to_integer((self.a as u32)))) == old(adler_spec_a(bytes, ((bytes.len() as u32) as i32), old(to_integer((self.a as u32))))) by normalize() using { adler_spec_a(bytes, ((bytes.len() as u32) as i32), old(to_integer((self.a as u32)))) == adler_spec_a(old(bytes), ((bytes.len() as u32) as i32), old(to_integer((self.a as u32)))); };
     have adler_spec_b(bytes, ((bytes.len() as u32) as i32), old(to_integer((self.a as u32))), old(to_integer((self.b as u32)))) == old(adler_spec_b(bytes, ((bytes.len() as u32) as i32), old(to_integer((self.a as u32))), old(to_integer((self.b as u32))))) by normalize() using { adler_spec_b(bytes, ((bytes.len() as u32) as i32), old(to_integer((self.a as u32))), old(to_integer((self.b as u32)))) == adler_spec_b(old(bytes), ((bytes.len() as u32) as i32), old(to_integer((self.a as u32))), old(to_integer((self.b as u32)))); };
     have truncating_remainder(to_integer(a), 65521) == old(adler_spec_a(bytes, ((bytes.len() as u32) as i32), old(to_integer((self.a as u32))))) by close() using { truncating_remainder(to_integer(a), 65521) == adler_spec_a(bytes, ((bytes.len() as u32) as i32), old(to_integer((self.a as u32)))); adler_spec_a(bytes, ((bytes.len() as u32) as i32), old(to_integer((self.a as u32)))) == old(adler_spec_a(bytes, ((bytes.len() as u32) as i32), old(to_integer((self.a as u32))))); };
     have truncating_remainder(to_integer(b), 65521) == old(adler_spec_b(bytes, ((bytes.len() as u32) as i32), old(to_integer((self.a as u32))), old(to_integer((self.b as u32))))) by close() using { truncating_remainder(to_integer(b), 65521) == adler_spec_b(bytes, ((bytes.len() as u32) as i32), old(to_integer((self.a as u32))), old(to_integer((self.b as u32)))); adler_spec_b(bytes, ((bytes.len() as u32) as i32), old(to_integer((self.a as u32))), old(to_integer((self.b as u32)))) == old(adler_spec_b(bytes, ((bytes.len() as u32) as i32), old(to_integer((self.a as u32))), old(to_integer((self.b as u32))))); };
     mark tail_done;
     have truncating_remainder(to_integer(at(tail_done, a)), 65521) == old(adler_spec_a(bytes, ((bytes.len() as u32) as i32), old(to_integer((self.a as u32))))) by normalize() using { truncating_remainder(to_integer(a), 65521) == old(adler_spec_a(bytes, ((bytes.len() as u32) as i32), old(to_integer((self.a as u32))))); };
     have truncating_remainder(to_integer(at(tail_done, b)), 65521) == old(adler_spec_b(bytes, ((bytes.len() as u32) as i32), old(to_integer((self.a as u32))), old(to_integer((self.b as u32))))) by normalize() using { truncating_remainder(to_integer(b), 65521) == old(adler_spec_b(bytes, ((bytes.len() as u32) as i32), old(to_integer((self.a as u32))), old(to_integer((self.b as u32))))); };

     apply(integer::uint32_remainder_to_integer(at(tail_done, a), 65521u32));
     have to_integer((at(tail_done, a) % 65521u32)) == truncating_remainder(to_integer(at(tail_done, a)), 65521) by close();
     have to_integer((at(tail_done, a) % 65521u32)) == old(adler_spec_a(bytes, ((bytes.len() as u32) as i32), old(to_integer((self.a as u32))))) by { rewrite(to_integer((at(tail_done, a) % 65521u32)), truncating_remainder(to_integer(at(tail_done, a)), 65521)); close(); }
     have (at(tail_done, a) % 65521u32) < 65521u32;
     have 0 <= to_integer((at(tail_done, a) % 65521u32));
     have to_integer((at(tail_done, a) % 65521u32)) <= 4294967295;
     have to_integer((at(tail_done, a) % 65521u32)) < 65521 by close() using { to_integer((at(tail_done, a) % 65521u32)) < to_integer(65521u32); };
     have to_integer((at(tail_done, a) % 65521u32)) <= 65535 by close() using { to_integer((at(tail_done, a) % 65521u32)) < 65521; };
     apply(integer::uint32_remainder_to_integer(at(tail_done, b), 65521u32));
     have to_integer((at(tail_done, b) % 65521u32)) == truncating_remainder(to_integer(at(tail_done, b)), 65521) by close();
     have to_integer((at(tail_done, b) % 65521u32)) == old(adler_spec_b(bytes, ((bytes.len() as u32) as i32), old(to_integer((self.a as u32))), old(to_integer((self.b as u32))))) by { rewrite(to_integer((at(tail_done, b) % 65521u32)), truncating_remainder(to_integer(at(tail_done, b)), 65521)); close(); }
     have (at(tail_done, b) % 65521u32) < 65521u32;
     have 0 <= to_integer((at(tail_done, b) % 65521u32));
     have to_integer((at(tail_done, b) % 65521u32)) <= 4294967295;
     have to_integer((at(tail_done, b) % 65521u32)) < 65521 by close() using { to_integer((at(tail_done, b) % 65521u32)) < to_integer(65521u32); };
     have to_integer((at(tail_done, b) % 65521u32)) <= 65535 by close() using { to_integer((at(tail_done, b) % 65521u32)) < 65521; };
     step_until(function.exit);
     have statement(22).call(0).result == 65521u32 by close();
     have self.a == ((at(tail_done, a) % statement(22).call(0).result) as u16) by close();
     have self.a == ((at(tail_done, a) % 65521u32) as u16) by { rewrite(self.a, ((at(tail_done, a) % statement(22).call(0).result) as u16)); rewrite(statement(22).call(0).result, 65521u32); close(); }
     have to_integer(self.a) == to_integer((at(tail_done, a) % 65521u32)) by { rewrite(self.a, ((at(tail_done, a) % 65521u32) as u16)); close() using { 0 <= to_integer((at(tail_done, a) % 65521u32)); to_integer((at(tail_done, a) % 65521u32)) <= 65535; }; }
     have to_integer(self.a) == old(adler_spec_a(bytes, ((bytes.len() as u32) as i32), old(to_integer((self.a as u32))))) by { rewrite(to_integer(self.a), to_integer((at(tail_done, a) % 65521u32))); close(); }
     have to_integer((at(tail_done, a) % 65521u32)) < 65521;
     have to_integer(self.a) < 65521 by { rewrite(to_integer(self.a), to_integer((at(tail_done, a) % 65521u32))); close(); }
     have statement(23).call(0).result == 65521u32 by close();
     have self.b == ((at(tail_done, b) % statement(23).call(0).result) as u16) by close();
     have self.b == ((at(tail_done, b) % 65521u32) as u16) by { rewrite(self.b, ((at(tail_done, b) % statement(23).call(0).result) as u16)); rewrite(statement(23).call(0).result, 65521u32); close(); }
     have to_integer(self.b) == to_integer((at(tail_done, b) % 65521u32)) by { rewrite(self.b, ((at(tail_done, b) % 65521u32) as u16)); close() using { 0 <= to_integer((at(tail_done, b) % 65521u32)); to_integer((at(tail_done, b) % 65521u32)) <= 65535; }; }
     have to_integer(self.b) == old(adler_spec_b(bytes, ((bytes.len() as u32) as i32), old(to_integer((self.a as u32))), old(to_integer((self.b as u32))))) by { rewrite(to_integer(self.b), to_integer((at(tail_done, b) % 65521u32))); close(); }
     have to_integer((at(tail_done, b) % 65521u32)) < 65521;
     have to_integer(self.b) < 65521 by { rewrite(to_integer(self.b), to_integer((at(tail_done, b) % 65521u32))); close(); }
     have 0 <= to_integer(self.a) by { rewrite(to_integer(self.a), to_integer((at(tail_done, a) % 65521u32))); close() using { 0 <= to_integer((at(tail_done, a) % 65521u32)); }; }
     have to_integer(self.a) <= 65535 by close() using { to_integer(self.a) < 65521; };
     have to_integer((self.a as i32)) == to_integer(self.a) by { close() using { 0 <= to_integer(self.a); to_integer(self.a) <= 65535; }; }
     have to_integer((self.a as i32)) <= to_integer(65520) by { rewrite(to_integer((self.a as i32)), to_integer(self.a)); close() using { to_integer(self.a) < 65521; }; }
     have ((self.a as i32)) <= 65520;
     apply(adler_i32_below_mod((self.a as i32)));
     have self.a < 65521 by close();
     have 0 <= to_integer(self.b) by { rewrite(to_integer(self.b), to_integer((at(tail_done, b) % 65521u32))); close() using { 0 <= to_integer((at(tail_done, b) % 65521u32)); }; }
     have to_integer(self.b) <= 65535 by close() using { to_integer(self.b) < 65521; };
     have to_integer((self.b as i32)) == to_integer(self.b) by { close() using { 0 <= to_integer(self.b); to_integer(self.b) <= 65535; }; }
     have to_integer((self.b as i32)) <= to_integer(65520) by { rewrite(to_integer((self.b as i32)), to_integer(self.b)); close() using { to_integer(self.b) < 65521; }; }
     have ((self.b as i32)) <= 65520;
     apply(adler_i32_below_mod((self.b as i32)));
     have self.b < 65521 by close();
     close() using { self.a < 65521; self.b < 65521; to_integer(self.a) == old(adler_spec_a(bytes, ((bytes.len() as u32) as i32), old(to_integer((self.a as u32))))); to_integer(self.b) == old(adler_spec_b(bytes, ((bytes.len() as u32) as i32), old(to_integer((self.a as u32))), old(to_integer((self.b as u32))))); };
    }
}
