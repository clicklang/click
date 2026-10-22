import click::integer;
import click::machine_integer;

// Checked split observations for composing two native slice updates.
// The two definedness facts, stated apart so the observations of the
// sum and the difference in `adler_incremental_split` are stated where they
// are established.
theorem adler_incremental_split_defined(total: uint64, prefix: uint64) {
 requires total <= 2147483647u64;
 requires prefix <= total;
 ensures defined((int32)(uint32)prefix + (int32)(uint32)(total - prefix)) and defined(2147483647 - (int32)(uint32)(total - prefix)) by {
  apply(uint64_to_integer_bounds(total));
  apply(uint64_to_integer_bounds(prefix));
  apply(uint64_less_equal_to_integer(prefix, total));
  apply(uint64_less_equal_to_integer(total, 2147483647u64));
  apply(uint64_subtract_to_integer(total, prefix));
  have to_integer(prefix) <= to_integer(2147483647u64) by arithmetic() using { to_integer(prefix) <= to_integer(total); to_integer(total) <= to_integer(2147483647u64); };
  apply(uint64_to_integer_less_equal_implies_less_equal(prefix, 2147483647u64));
  have to_integer(total - prefix) <= to_integer(2147483647u64) by arithmetic() using { to_integer(total - prefix) == to_integer(total) - to_integer(prefix); 0 <= to_integer(prefix); to_integer(total) <= to_integer(2147483647u64); };
  apply(uint64_to_integer_less_equal_implies_less_equal(total - prefix, 2147483647u64));
  apply(adler_bounded_count(total));
  apply(adler_bounded_count(prefix));
  apply(adler_bounded_count(total - prefix));
  have to_integer((int32)(uint32)prefix) + to_integer((int32)(uint32)(total - prefix)) == to_integer((int32)(uint32)total) by arithmetic() using {
   to_integer((int32)(uint32)prefix) == to_integer(prefix);
   to_integer((int32)(uint32)(total - prefix)) == to_integer(total - prefix);
   to_integer(total - prefix) == to_integer(total) - to_integer(prefix);
   to_integer((int32)(uint32)total) == to_integer(total);
  };
  have to_integer((int32)(uint32)prefix) + to_integer((int32)(uint32)(total - prefix)) >= -2147483648 by arithmetic() using { to_integer((int32)(uint32)prefix) + to_integer((int32)(uint32)(total - prefix)) == to_integer((int32)(uint32)total); to_integer((int32)(uint32)total) == to_integer(total); 0 <= to_integer(total); };
  have to_integer((int32)(uint32)prefix) + to_integer((int32)(uint32)(total - prefix)) <= 2147483647 by arithmetic() using { to_integer((int32)(uint32)prefix) + to_integer((int32)(uint32)(total - prefix)) == to_integer((int32)(uint32)total); to_integer((int32)(uint32)total) == to_integer(total); to_integer(total) <= to_integer(2147483647u64); };
  apply(int32_add_defined_by_integer_bounds((int32)(uint32)prefix, (int32)(uint32)(total - prefix)));
  have to_integer(2147483647) - to_integer((int32)(uint32)(total - prefix)) >= -2147483648 by arithmetic() using { to_integer((int32)(uint32)(total - prefix)) == to_integer(total - prefix); to_integer(total - prefix) <= to_integer(2147483647u64); };
  have to_integer(2147483647) - to_integer((int32)(uint32)(total - prefix)) <= 2147483647 by arithmetic() using { to_integer((int32)(uint32)(total - prefix)) == to_integer(total - prefix); to_integer(total - prefix) == to_integer(total) - to_integer(prefix); to_integer(prefix) <= to_integer(total); };
  apply(int32_subtract_defined_by_integer_bounds(2147483647, (int32)(uint32)(total - prefix)));
  both { assumption(); } and { assumption(); }
 }
}

theorem adler_incremental_split(total: uint64, prefix: uint64) {
 requires total <= 2147483647u64;
 requires prefix <= total;
 requires defined((int32)(uint32)prefix + (int32)(uint32)(total - prefix));
 requires defined(2147483647 - (int32)(uint32)(total - prefix));
 ensures prefix <= 2147483647u64 and to_integer(total - prefix) <= to_integer(2147483647u64) and
         0 <= (int32)(uint32)prefix and 0 <= (int32)(uint32)(total - prefix) and
         defined((int32)(uint32)prefix + (int32)(uint32)(total - prefix)) and
         (int32)(uint32)prefix + (int32)(uint32)(total - prefix) == (int32)(uint32)total and
         to_integer((int32)(uint32)prefix) <= to_integer(2147483647 - (int32)(uint32)(total - prefix)) by {
  apply(uint64_to_integer_bounds(total));
  apply(uint64_to_integer_bounds(prefix));
  apply(uint64_less_equal_to_integer(prefix, total));
  apply(uint64_less_equal_to_integer(total, 2147483647u64));
  apply(uint64_subtract_to_integer(total, prefix));
  have to_integer(prefix) <= to_integer(2147483647u64) by arithmetic() using { to_integer(prefix) <= to_integer(total); to_integer(total) <= to_integer(2147483647u64); };
  apply(uint64_to_integer_less_equal_implies_less_equal(prefix, 2147483647u64));
  have to_integer(total - prefix) <= to_integer(2147483647u64) by arithmetic() using { to_integer(total - prefix) == to_integer(total) - to_integer(prefix); 0 <= to_integer(prefix); to_integer(total) <= to_integer(2147483647u64); };
  apply(uint64_to_integer_less_equal_implies_less_equal(total - prefix, 2147483647u64));
  apply(adler_bounded_count(total));
  apply(adler_bounded_count(prefix));
  apply(adler_bounded_count(total - prefix));
  have to_integer((int32)(uint32)prefix) + to_integer((int32)(uint32)(total - prefix)) == to_integer((int32)(uint32)total) by arithmetic() using {
   to_integer((int32)(uint32)prefix) == to_integer(prefix);
   to_integer((int32)(uint32)(total - prefix)) == to_integer(total - prefix);
   to_integer(total - prefix) == to_integer(total) - to_integer(prefix);
   to_integer((int32)(uint32)total) == to_integer(total);
  };
  have to_integer((int32)(uint32)prefix) + to_integer((int32)(uint32)(total - prefix)) >= -2147483648 by arithmetic() using { to_integer((int32)(uint32)prefix) + to_integer((int32)(uint32)(total - prefix)) == to_integer((int32)(uint32)total); to_integer((int32)(uint32)total) == to_integer(total); 0 <= to_integer(total); };
  have to_integer((int32)(uint32)prefix) + to_integer((int32)(uint32)(total - prefix)) <= 2147483647 by arithmetic() using { to_integer((int32)(uint32)prefix) + to_integer((int32)(uint32)(total - prefix)) == to_integer((int32)(uint32)total); to_integer((int32)(uint32)total) == to_integer(total); to_integer(total) <= to_integer(2147483647u64); };
  apply(int32_add_defined_by_integer_bounds((int32)(uint32)prefix, (int32)(uint32)(total - prefix)));
  have defined((int32)(uint32)prefix + (int32)(uint32)(total - prefix)) by assumption();
  have to_integer(total) - to_integer(prefix) <= to_integer(2147483647u64) by arithmetic() using { to_integer(total - prefix) == to_integer(total) - to_integer(prefix); to_integer(total - prefix) <= to_integer(2147483647u64); };
  have to_integer((int32)(uint32)prefix) <= 2147483647 - to_integer((int32)(uint32)(total - prefix)) by arithmetic() using { to_integer((int32)(uint32)prefix) + to_integer((int32)(uint32)(total - prefix)) <= 2147483647; };
  apply(int32_subtract_to_integer(2147483647, (int32)(uint32)(total - prefix))) using { defined(2147483647 - (int32)(uint32)(total - prefix)); };
  have to_integer((int32)(uint32)prefix) <= to_integer(2147483647 - (int32)(uint32)(total - prefix)) by arithmetic() using { to_integer(2147483647 - (int32)(uint32)(total - prefix)) == to_integer(2147483647) - to_integer((int32)(uint32)(total - prefix)); to_integer((int32)(uint32)prefix) <= 2147483647 - to_integer((int32)(uint32)(total - prefix)); };
  simp();
 }
}
