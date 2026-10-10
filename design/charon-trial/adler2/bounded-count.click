# Checked signed observations of native counts within the explicit signed limit.
# Iterator state and slice metadata retain their full unsigned 64-bit width.
theorem adler_bounded_count(count: uint64) {
 requires count <= 2147483647u64;
 ensures to_integer((int32)(uint32)count) == to_integer(count) by {
  apply(uint64_to_integer_bounds(count));
  apply(uint64_less_equal_to_integer(count, 2147483647u64));
  arithmetic_certificate special {
   premise 0: 0 <= to_integer(count) => 0 <= to_integer(count);
   premise 1: to_integer(count) <= 2147483647 => to_integer(count) <= 2147483647;
   integer_cast_identity bounds [0, 1] => to_integer((int32)(uint32)count) == to_integer(count);
   conclusion 0;
  }
 }
 ensures 0 <= (int32)(uint32)count by {
  apply(uint64_to_integer_bounds(count));
  apply(uint64_less_equal_to_integer(count, 2147483647u64));
  have to_integer((int32)(uint32)count) == to_integer(count) by {
   arithmetic_certificate special {
    premise 0: 0 <= to_integer(count) => 0 <= to_integer(count);
    premise 1: to_integer(count) <= 2147483647 => to_integer(count) <= 2147483647;
    integer_cast_identity bounds [0, 1] => to_integer((int32)(uint32)count) == to_integer(count);
    conclusion 0;
   }
  }
  have 0 <= to_integer((int32)(uint32)count) by { rewrite(to_integer((int32)(uint32)count) == to_integer(count)); assumption(); }
  apply(int32_less_equal_of_to_integer(0, (int32)(uint32)count)); assumption();
 }
 ensures (uint64)(int32)(uint32)count == count by {
  apply(uint64_to_integer_bounds(count));
  apply(uint64_less_equal_to_integer(count, 2147483647u64));
  have to_integer((int32)(uint32)count) == to_integer(count) by {
   arithmetic_certificate special {
    premise 0: 0 <= to_integer(count) => 0 <= to_integer(count);
    premise 1: to_integer(count) <= 2147483647 => to_integer(count) <= 2147483647;
    integer_cast_identity bounds [0, 1] => to_integer((int32)(uint32)count) == to_integer(count);
    conclusion 0;
   }
  }
  have 0 <= to_integer((int32)(uint32)count) by { rewrite(to_integer((int32)(uint32)count) == to_integer(count)); assumption(); }
  have to_integer((int32)(uint32)count) <= 2147483647 by { rewrite(to_integer((int32)(uint32)count) == to_integer(count)); assumption(); }
  have to_integer((uint64)(int32)(uint32)count) == to_integer((int32)(uint32)count) by {
   arithmetic_certificate special {
    premise 0: 0 <= to_integer((int32)(uint32)count) => 0 <= to_integer((int32)(uint32)count);
    premise 1: to_integer((int32)(uint32)count) <= 2147483647 => to_integer((int32)(uint32)count) <= 2147483647;
    integer_cast_identity bounds [0, 1] => to_integer((uint64)(int32)(uint32)count) == to_integer((int32)(uint32)count);
    conclusion 0;
   }
  }
  have to_integer((uint64)(int32)(uint32)count) == to_integer(count) by { rewrite(to_integer((uint64)(int32)(uint32)count) == to_integer((int32)(uint32)count)); assumption(); }
  apply(uint64_equal_of_to_integer((uint64)(int32)(uint32)count, count)); assumption();
 }
}


theorem adler_bounded_pointer_index(base: const uint8*, count: uint64) {
 requires count <= 2147483647u64;
 ensures base + count == base + (int32)(uint32)count by {
  apply(adler_bounded_count(count));
  simp() using { to_integer((int32)(uint32)count) == to_integer(count); (uint64)(int32)(uint32)count == count; 0 <= (int32)(uint32)count; count <= 2147483647u64; }
 }
}

theorem adler_bounded_count_lower(count: uint64, low: int32) {
 requires count <= 2147483647u64;
 requires 0 <= low;
 requires (uint64)low <= count;
 ensures low <= (int32)(uint32)count by {
  apply(adler_bounded_count(count));
  apply(int32_less_equal_to_integer(0, low));
  have low <= 2147483647 by { normalize(); }
  apply(int32_less_equal_to_integer(low, 2147483647));
  have to_integer((uint64)low) == to_integer(low) by {
   arithmetic_certificate special {
    premise 0: 0 <= to_integer(low) => 0 <= to_integer(low);
    premise 1: to_integer(low) <= 2147483647 => to_integer(low) <= 2147483647;
    integer_cast_identity bounds [0, 1] => to_integer((uint64)low) == to_integer(low);
    conclusion 0;
   }
  }
  apply(uint64_less_equal_to_integer((uint64)low, count));
  have to_integer(low) <= to_integer((int32)(uint32)count) by {
   rewrite(to_integer((int32)(uint32)count) == to_integer(count));
   rewrite(to_integer(low) == to_integer((uint64)low));
   assumption();
  }
  apply(int32_less_equal_of_to_integer(low, (int32)(uint32)count)); assumption();
 }
}

theorem adler_bounded_count_upper(count: uint64, high: int32) {
 requires count <= 2147483647u64;
 requires 0 <= high;
 requires count <= (uint64)high;
 ensures (int32)(uint32)count <= high by {
  apply(adler_bounded_count(count));
  apply(int32_less_equal_to_integer(0, high));
  have high <= 2147483647 by { normalize(); }
  apply(int32_less_equal_to_integer(high, 2147483647));
  have to_integer((uint64)high) == to_integer(high) by {
   arithmetic_certificate special {
    premise 0: 0 <= to_integer(high) => 0 <= to_integer(high);
    premise 1: to_integer(high) <= 2147483647 => to_integer(high) <= 2147483647;
    integer_cast_identity bounds [0, 1] => to_integer((uint64)high) == to_integer(high);
    conclusion 0;
   }
  }
  apply(uint64_less_equal_to_integer(count, (uint64)high));
  have to_integer((int32)(uint32)count) <= to_integer(high) by {
   rewrite(to_integer((int32)(uint32)count) == to_integer(count));
   rewrite(to_integer(high) == to_integer((uint64)high));
   assumption();
  }
  apply(int32_less_equal_of_to_integer((int32)(uint32)count, high)); assumption();
 }
}

theorem adler_bounded_count_native_lower(count: uint64, low: int32) {
 requires count <= 2147483647u64;
 requires 0 <= low;
 requires low <= (int32)(uint32)count;
 ensures (uint64)low <= count by {
  apply(adler_bounded_count(count));
  apply(int32_less_equal_to_integer(0, low));
  have low <= 2147483647 by { normalize(); }
  apply(int32_less_equal_to_integer(low, 2147483647));
  have to_integer((uint64)low) == to_integer(low) by {
   arithmetic_certificate special {
    premise 0: 0 <= to_integer(low) => 0 <= to_integer(low);
    premise 1: to_integer(low) <= 2147483647 => to_integer(low) <= 2147483647;
    integer_cast_identity bounds [0, 1] => to_integer((uint64)low) == to_integer(low);
    conclusion 0;
   }
  }
  apply(int32_less_equal_to_integer(low, (int32)(uint32)count));
  have to_integer((uint64)low) <= to_integer(count) by {
   rewrite(to_integer((uint64)low) == to_integer(low));
   rewrite(to_integer(count) == to_integer((int32)(uint32)count));
   assumption();
  }
  apply(uint64_less_equal_of_to_integer((uint64)low, count)); assumption();
 }
}
