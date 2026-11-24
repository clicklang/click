// Local unsigned-word laws used by explicit tagged-address proofs. Arithmetic
// in these laws is modulo 2^64; the mask guards are stated as word equations.
axiom uint64_and_commute(a: uint64, b: uint64) {
    ensures (a & b) == (b & a);
}
axiom uint64_and_associate(a: uint64, b: uint64, c: uint64) {
    ensures ((a & b) & c) == (a & (b & c));
}
axiom uint64_or_commute(a: uint64, b: uint64) {
    ensures (a | b) == (b | a);
}
axiom uint64_and_or(a: uint64, b: uint64, mask: uint64) {
    ensures ((a | b) & mask) == ((a & mask) | (b & mask));
}
theorem uint64_and_zero(a: uint64) {
    ensures (a & 0u64) == 0u64 by close();
}
theorem uint64_or_zero(a: uint64) {
    ensures (a | 0u64) == a by close();
}
axiom uint64_or_disjoint(a: uint64, b: uint64) {
    requires (a & b) == 0u64;
    ensures (a | b) == ((a + b) as uint64);
}
axiom uint64_mask_add_low(base: uint64, tag: uint64, mask: uint64) {
    requires (mask & (mask + 1u64)) == 0u64;
    requires (base & mask) == 0u64;
    ensures ((base + tag) & mask) == (tag & mask);
}
axiom uint64_mask_add_high(base: uint64, tag: uint64, mask: uint64) {
    requires ((~mask) & ((~mask) + 1u64)) == 0u64;
    requires (base & (~mask)) == 0u64;
    ensures ((base + tag) & mask) == ((base + (tag & mask)) as uint64);
}
axiom uint64_mask_multiple(value: uint64, factor: uint64, mask: uint64) {
    requires (mask & (mask + 1u64)) == 0u64;
    requires (factor & mask) == 0u64;
    ensures ((value * factor) & mask) == 0u64;
}
axiom uint64_mask_keep(base: uint64, mask: uint64) {
    requires (base & (~mask)) == 0u64;
    ensures (base & mask) == base;
}
axiom uint64_mask_add_clear(base: uint64, tag: uint64, mask: uint64) {
    requires ((~mask) & ((~mask) + 1u64)) == 0u64;
    requires (base & (~mask)) == 0u64;
    requires (tag & mask) == 0u64;
    ensures ((base + tag) & mask) == base;
}
axiom uint64_add_distinct(base: uint64, a: uint64, b: uint64) {
    requires a != b;
    ensures ((base + a) as uint64) != ((base + b) as uint64);
}
axiom uint64_add_subtract_cancel(a: uint64, b: uint64) {
    ensures ((((a + b) as uint64) - a) as uint64) == b;
}
axiom uint64_or_add_low(base: uint64, tag: uint64, bits: uint64, mask: uint64) {
    requires (mask & (mask + 1u64)) == 0u64;
    requires (base & mask) == 0u64;
    requires (bits & mask) == bits;
    ensures ((base + tag) | bits) == ((base + (tag | bits)) as uint64);
}

theorem uint64_mask_subset(base: uint64, large: uint64, small: uint64) {
    requires (base & large) == 0u64;
    requires (large & small) == small;
    ensures (base & small) == 0u64 by {
        apply(integer::uint64_and_associate(base, large, small));
        apply(integer::uint64_and_commute(0u64, small));
        rewrite(small, large & small);
        rewrite(base & (large & small), (base & large) & small);
        rewrite(base & large, 0u64);
        rewrite(0u64 & small, small & 0u64);
        close();
    }
}

theorem uint64_or_masked(base: uint64, tag: uint64, mask: uint64) {
    requires (base & mask) == 0u64;
    ensures (base | (tag & mask)) == ((base + (tag & mask)) as uint64) by {
        have (base & (tag & mask)) == 0u64 by {
            apply(integer::uint64_and_commute(tag, mask));
            apply(integer::uint64_and_associate(base, mask, tag));
            apply(integer::uint64_and_commute(0u64, tag));
            rewrite(tag & mask, mask & tag);
            rewrite(base & (mask & tag), (base & mask) & tag);
            rewrite(base & mask, 0u64);
            rewrite(0u64 & tag, tag & 0u64);
            close();
        }
        apply(integer::uint64_or_disjoint(base, tag & mask));
    }
}

// Address observations respect element offsets independently of memory contents.
axiom uint8_pointer_add_address_int32(p: uint8*, index: int32) {
    ensures address(p + index) == ((address(p) + (index as uint64) * 1u64) as uint64);
}
axiom uint8_pointer_add_address_int64(p: uint8*, index: int64) {
    ensures address(p + index) == ((address(p) + (index as uint64) * 1u64) as uint64);
}
axiom uint8_pointer_add_address_uint64(p: uint8*, index: uint64) {
    ensures address(p + index) == ((address(p) + index * 1u64) as uint64);
}
axiom int8_pointer_add_address_int32(p: int8*, index: int32) {
    ensures address(p + index) == ((address(p) + (index as uint64) * 1u64) as uint64);
}
axiom int8_pointer_add_address_int64(p: int8*, index: int64) {
    ensures address(p + index) == ((address(p) + (index as uint64) * 1u64) as uint64);
}
axiom int8_pointer_add_address_uint64(p: int8*, index: uint64) {
    ensures address(p + index) == ((address(p) + index * 1u64) as uint64);
}
axiom uint16_pointer_add_address_int32(p: uint16*, index: int32) {
    ensures address(p + index) == ((address(p) + (index as uint64) * 2u64) as uint64);
}
axiom uint16_pointer_add_address_int64(p: uint16*, index: int64) {
    ensures address(p + index) == ((address(p) + (index as uint64) * 2u64) as uint64);
}
axiom uint16_pointer_add_address_uint64(p: uint16*, index: uint64) {
    ensures address(p + index) == ((address(p) + index * 2u64) as uint64);
}
axiom int16_pointer_add_address_int32(p: int16*, index: int32) {
    ensures address(p + index) == ((address(p) + (index as uint64) * 2u64) as uint64);
}
axiom int16_pointer_add_address_int64(p: int16*, index: int64) {
    ensures address(p + index) == ((address(p) + (index as uint64) * 2u64) as uint64);
}
axiom int16_pointer_add_address_uint64(p: int16*, index: uint64) {
    ensures address(p + index) == ((address(p) + index * 2u64) as uint64);
}
axiom uint32_pointer_add_address_int32(p: uint32*, index: int32) {
    ensures address(p + index) == ((address(p) + (index as uint64) * 4u64) as uint64);
}
axiom uint32_pointer_add_address_int64(p: uint32*, index: int64) {
    ensures address(p + index) == ((address(p) + (index as uint64) * 4u64) as uint64);
}
axiom uint32_pointer_add_address_uint64(p: uint32*, index: uint64) {
    ensures address(p + index) == ((address(p) + index * 4u64) as uint64);
}
axiom int32_pointer_add_address_int32(p: int32*, index: int32) {
    ensures address(p + index) == ((address(p) + (index as uint64) * 4u64) as uint64);
}
axiom int32_pointer_add_address_int64(p: int32*, index: int64) {
    ensures address(p + index) == ((address(p) + (index as uint64) * 4u64) as uint64);
}
axiom int32_pointer_add_address_uint64(p: int32*, index: uint64) {
    ensures address(p + index) == ((address(p) + index * 4u64) as uint64);
}
axiom uint64_pointer_add_address_int32(p: uint64*, index: int32) {
    ensures address(p + index) == ((address(p) + (index as uint64) * 8u64) as uint64);
}
axiom uint64_pointer_add_address_int64(p: uint64*, index: int64) {
    ensures address(p + index) == ((address(p) + (index as uint64) * 8u64) as uint64);
}
axiom uint64_pointer_add_address_uint64(p: uint64*, index: uint64) {
    ensures address(p + index) == ((address(p) + index * 8u64) as uint64);
}
axiom int64_pointer_add_address_int32(p: int64*, index: int32) {
    ensures address(p + index) == ((address(p) + (index as uint64) * 8u64) as uint64);
}
axiom int64_pointer_add_address_int64(p: int64*, index: int64) {
    ensures address(p + index) == ((address(p) + (index as uint64) * 8u64) as uint64);
}
axiom int64_pointer_add_address_uint64(p: int64*, index: uint64) {
    ensures address(p + index) == ((address(p) + index * 8u64) as uint64);
}
axiom float32_pointer_add_address_int32(p: float*, index: int32) {
    ensures address(p + index) == ((address(p) + (index as uint64) * 4u64) as uint64);
}
axiom float32_pointer_add_address_int64(p: float*, index: int64) {
    ensures address(p + index) == ((address(p) + (index as uint64) * 4u64) as uint64);
}
axiom float32_pointer_add_address_uint64(p: float*, index: uint64) {
    ensures address(p + index) == ((address(p) + index * 4u64) as uint64);
}
axiom float64_pointer_add_address_int32(p: double*, index: int32) {
    ensures address(p + index) == ((address(p) + (index as uint64) * 8u64) as uint64);
}
axiom float64_pointer_add_address_int64(p: double*, index: int64) {
    ensures address(p + index) == ((address(p) + (index as uint64) * 8u64) as uint64);
}
axiom float64_pointer_add_address_uint64(p: double*, index: uint64) {
    ensures address(p + index) == ((address(p) + index * 8u64) as uint64);
}

// Explicit multiplicative laws used by ordinary algebra expansion.
axiom multiply_commutative(a: Integer, b: Integer) {
    ensures a * b == b * a;
}

axiom multiply_negate(a: Integer, b: Integer) {
    ensures a * -b == -(a * b);
}

axiom multiply_add(a: Integer, b: Integer, c: Integer) {
    ensures (a + b) * c == a * c + b * c;
}

axiom multiply_associative(a: Integer, b: Integer, c: Integer) {
    ensures (a * b) * c == a * (b * c);
}

theorem multiply_add_left(a: Integer, b: Integer, c: Integer) {
    ensures a * (b + c) == a * b + a * c by {
        apply(integer::multiply_commutative(a, b + c));
        apply(integer::multiply_add(b, c, a));
        apply(integer::multiply_commutative(b, a));
        apply(integer::multiply_commutative(c, a));
        close();
    }
}

theorem negate_as_product(a: Integer) {
    ensures -a == -1 * a by {
        apply(integer::multiply_negate(a, 1));
        apply(integer::multiply_commutative(-1, a));
        have a * 1 == a by close();
        close();
    }
}

theorem multiply_swap_front(a: Integer, b: Integer, c: Integer) {
    ensures a * (b * c) == b * (a * c) by {
        apply(integer::multiply_associative(a, b, c));
        apply(integer::multiply_commutative(a, b));
        apply(integer::multiply_associative(b, a, c));
        close();
    }
}

// Foundational Integer order laws, available through ordinary explicit application.
axiom add_le(a: Integer, b: Integer, c: Integer, d: Integer) {
    requires a <= b;
    requires c <= d;
    ensures a + c <= b + d;
}

axiom le_antisymmetric(a: Integer, b: Integer) {
    requires a <= b;
    requires b <= a;
    ensures a == b;
}

// Discreteness of exact Integer order, already used by strict arithmetic
// certificate premises. The reverse implication is proved below.
axiom lt_step_le(a: Integer, b: Integer) {
    requires a < b;
    ensures a + 1 <= b;
}

theorem step_le_lt(a: Integer, b: Integer) {
    requires a + 1 <= b;
    ensures a < b by {
        if a < b {
            close();
        } else {
            have b <= a by { close(); }
            have a + 1 + b <= b + a by {
                apply(integer::add_le(a + 1, b, b, a));
            }
            contradiction(a + 1 + b <= b + a);
        }
    }
}

theorem le_ne_lt(a: Integer, b: Integer) {
    requires a <= b;
    requires a != b;
    ensures a < b by {
        if a < b {
            close();
        } else {
            have b <= a by { close(); }
            have a == b by {
                apply(integer::le_antisymmetric(a, b));
            }
            contradiction(a == b);
        }
    }
}

// Congruence helpers are ordinary proved theorems. Applying a generic
// substitution theorem also works when a concrete equality evaluates to true.
theorem le_substitute(a: Integer, b: Integer, c: Integer, d: Integer) {
    requires a <= b;
    requires c == a;
    requires d == b;
    ensures c <= d by { rewrite(c, a); rewrite(d, b); close(); }
}

theorem equal_substitute(a: Integer, b: Integer, c: Integer, d: Integer) {
    requires a == b;
    requires c == a;
    requires d == b;
    ensures c == d by { rewrite(c, a); rewrite(d, b); close(); }
}

theorem le_difference(a:Integer,b:Integer,value:Integer) {
 requires a<=b;
 requires value==a-b;
 ensures value<=0 by {
  have a + -b <= b + -b by {
   apply(click::integer::add_le(a,b,-b,-b));
  }
  have value == a + -b by { rewrite(value,a-b); close(); }
  have 0 == b + -b by close();
  apply(click::integer::le_substitute(a + -b,b + -b,value,0));
 }
}
theorem difference_le(a:Integer,b:Integer,value:Integer) {
 requires value<=0;
 requires value==a-b;
 ensures a<=b by {
  have value + b <= 0 + b by {
   apply(click::integer::add_le(value,0,b,b));
  }
  have a == value + b by { rewrite(value,a-b); close(); }
  have b == 0 + b by close();
  apply(click::integer::le_substitute(value+b,0+b,a,b));
 }
}

theorem equal_difference(a: Integer, b: Integer) {
    requires a == b;
    ensures a - b == 0 by { rewrite(a, b); close(); }
}

theorem equal_add(a: Integer, b: Integer, c: Integer, d: Integer) {
    requires a == b;
    requires c == d;
    ensures a + c == b + d by { rewrite(a, b); rewrite(c, d); close(); }
}

theorem equal_multiply(a: Integer, b: Integer, factor: Integer) {
    requires a == b;
    ensures a * factor == b * factor by { rewrite(a, b); close(); }
}

theorem equal_negate(a: Integer, b: Integer) {
    requires a == b;
    ensures -a == -b by {
        rewrite(a, b);
        close();
    }
}

theorem equal_le(a: Integer, b: Integer) {
    requires a == b;
    ensures a <= b by { rewrite(a, b); close(); }
}

// No nonnegativity assumption on the remainder is needed for this upper
// bound. The strict upper bound and positive divisor are both essential.
axiom round_down_le(value: Integer, bound: Integer, divisor: Integer, remainder: Integer) {
    requires 0 < divisor;
    requires remainder < divisor;
    requires value * divisor <= bound * divisor + remainder;
    ensures value <= bound;
}

// Neither `bound - value` nor `(bound - 1) - value` wraps under
// `value < bound`, so the measure drops by exactly one.
axiom uint32_difference_decreases_after_increment(value: uint32, bound: uint32) {
    requires value < bound;
    ensures to_integer((0u32 - value) + (bound - 1u32)) < to_integer((0u32 - value) + bound);
}

theorem int32_less_equal_and_not_less_than_implies_equal(left: int32, right: int32) {
    requires left <= right;
    requires not (left < right);

    ensures left == right by {
        have to_integer(right) <= to_integer(left) by close();
        apply(integer::le_antisymmetric(to_integer(left), to_integer(right)));
        close();
    }
}

theorem int32_less_equal_and_not_equal_implies_less_than(left: int32, right: int32) {
    requires left <= right;
    requires left != right;

    ensures left < right by {
        have to_integer(left) != to_integer(right) by close();
        apply(integer::le_ne_lt(to_integer(left), to_integer(right)));
        close();
    }
}

// Wrapping unsigned arithmetic, the C operation itself. A specification that
// means C's modular result writes it with these, so it keeps that meaning
// where `+`, `-` and `*` compare exact Integers.
function uint32_wrapping_add(left: uint32, right: uint32) -> uint32 {
    left + right
}

function uint32_wrapping_sub(left: uint32, right: uint32) -> uint32 {
    left - right
}

function uint32_wrapping_mul(left: uint32, right: uint32) -> uint32 {
    left * right
}

function uint64_wrapping_add(left: uint64, right: uint64) -> uint64 {
    left + right
}

function uint64_wrapping_sub(left: uint64, right: uint64) -> uint64 {
    left - right
}

function uint64_wrapping_mul(left: uint64, right: uint64) -> uint64 {
    left * right
}

axiom multiply_order_nonnegative(a: Integer, b: Integer, factor: Integer) {
    requires a <= b;
    requires 0 <= factor;
    ensures a * factor <= b * factor;
}

theorem negate_order(a: Integer, b: Integer) {
    requires a <= b;
    ensures -b <= -a by {
        have a + (-a + -b) <= b + (-a + -b) by {
            apply(integer::add_le(a, b, -a + -b, -a + -b));
        }
        have -b == a + (-a + -b) by { close(); }
        have -a == b + (-a + -b) by { close(); }
        rewrite(-b, a + (-a + -b));
        rewrite(-a, b + (-a + -b));
        close();
    }
}

theorem uint32_add_to_integer(left: uint32, right: uint32) {
    requires to_integer(left) + to_integer(right) <= 4294967295;
    ensures to_integer(left + right) == to_integer(left) + to_integer(right) by {
        have 0 <= to_integer(left) by close();
        have 0 <= to_integer(right) by close();
        have 0 + 0 <= (to_integer(left) + to_integer(right)) by {
            apply(integer::add_le(0, to_integer(left), 0, to_integer(right)));
        }
        have 0 <= (to_integer(left) + to_integer(right)) by close();
        close();
    }
}

// Exact unsigned subtraction needs the native no-underflow guard.
theorem uint32_subtract_to_integer(left: uint32, right: uint32) {
    requires right <= left;
    ensures to_integer(left - right) == to_integer(left) - to_integer(right) by {
        have to_integer(right) <= to_integer(left) by close();
        have 0 <= to_integer(right) by close();
        have to_integer(left) <= 4294967295 by close();
        have to_integer(right) + -to_integer(right) <= (to_integer(left) + -to_integer(right)) by {
            apply(integer::add_le(to_integer(right), to_integer(left), -to_integer(right), -to_integer(right)));
        }
        have 0 == to_integer(right) + -to_integer(right) by close();
        have (to_integer(left) - to_integer(right)) == (to_integer(left) + -to_integer(right)) by close();
        have 0 <= (to_integer(left) - to_integer(right)) by {
            apply(integer::le_substitute(to_integer(right) + -to_integer(right), (to_integer(left) + -to_integer(right)), 0, (to_integer(left) - to_integer(right))));
        }
        have -to_integer(right) <= 0 by {
            apply(integer::negate_order(0, to_integer(right)));
            close();
        }
        have (to_integer(left) + -to_integer(right)) <= 4294967295 + 0 by {
            apply(integer::add_le(to_integer(left), 4294967295, -to_integer(right), 0));
        }
        have to_integer(4294967295u64) == 4294967295 + 0 by close();
        have (to_integer(left) - to_integer(right)) <= 4294967295 by {
            apply(integer::le_substitute((to_integer(left) + -to_integer(right)), 4294967295 + 0, (to_integer(left) - to_integer(right)), 4294967295));
        }
        close();
    }
}

theorem uint64_add_to_integer(left: uint64, right: uint64) {
    requires to_integer(left) + to_integer(right) <= 18446744073709551615;
    ensures to_integer(left + right) == to_integer(left) + to_integer(right) by {
        have 0 <= to_integer(left) by close();
        have 0 <= to_integer(right) by close();
        have 0 + 0 <= (to_integer(left) + to_integer(right)) by {
            apply(integer::add_le(0, to_integer(left), 0, to_integer(right)));
        }
        have 0 <= (to_integer(left) + to_integer(right)) by close();
        close();
    }
}

theorem uint64_multiply_to_integer(left: uint64, right: uint64) {
    requires to_integer(left) * to_integer(right) <= 18446744073709551615;
    ensures to_integer(left * right) == to_integer(left) * to_integer(right) by {
        have 0 <= to_integer(left) by close();
        have 0 <= to_integer(right) by close();
        have 0 * to_integer(right) <= (to_integer(left) * to_integer(right)) by {
            apply(integer::multiply_order_nonnegative(0, to_integer(left), to_integer(right)));
        }
        have 0 <= (to_integer(left) * to_integer(right)) by close();
        close();
    }
}

theorem uint64_subtract_to_integer(left: uint64, right: uint64) {
    requires to_integer(right) <= to_integer(left);
    ensures to_integer(left - right) == to_integer(left) - to_integer(right) by {
        have to_integer(right) <= to_integer(left) by close();
        have 0 <= to_integer(right) by close();
        have to_integer(left) <= 18446744073709551615 by close();
        have to_integer(right) + -to_integer(right) <= (to_integer(left) + -to_integer(right)) by {
            apply(integer::add_le(to_integer(right), to_integer(left), -to_integer(right), -to_integer(right)));
        }
        have 0 == to_integer(right) + -to_integer(right) by close();
        have (to_integer(left) - to_integer(right)) == (to_integer(left) + -to_integer(right)) by close();
        have 0 <= (to_integer(left) - to_integer(right)) by {
            apply(integer::le_substitute(to_integer(right) + -to_integer(right), (to_integer(left) + -to_integer(right)), 0, (to_integer(left) - to_integer(right))));
        }
        have -to_integer(right) <= 0 by {
            apply(integer::negate_order(0, to_integer(right)));
            close();
        }
        have (to_integer(left) + -to_integer(right)) <= 18446744073709551615 + 0 by {
            apply(integer::add_le(to_integer(left), 18446744073709551615, -to_integer(right), 0));
        }
        have to_integer(18446744073709551615u64) == 18446744073709551615 + 0 by close();
        have (to_integer(left) - to_integer(right)) <= 18446744073709551615 by {
            apply(integer::le_substitute((to_integer(left) + -to_integer(right)), 18446744073709551615 + 0, (to_integer(left) - to_integer(right)), 18446744073709551615));
        }
        close();
    }
}

theorem uint64_divide_to_integer(left: uint64, right: uint64) {
    requires right != 0u64;
    requires to_integer(right) != 0;
    ensures to_integer(left / right) == truncating_quotient(to_integer(left), to_integer(right));
}

theorem uint64_remainder_to_integer(left: uint64, right: uint64) {
    requires right != 0u64;
    requires to_integer(right) != 0;
    ensures to_integer(left % right) == truncating_remainder(to_integer(left), to_integer(right));
}

theorem uint64_to_integer_less_equal_implies_less_equal(left: uint64, right: uint64) {
    requires to_integer(left) <= to_integer(right);
    ensures left <= right by close();
}

theorem uint32_pack_uint16_to_integer(low: uint32, high: uint32) {
    requires low <= 65535u32;
    requires high <= 65535u32;
    ensures to_integer(low | (high << 16)) == to_integer(low) + 65536 * to_integer(high);
}

theorem uint32_pack_uint16_high_first_to_integer(low: uint32, high: uint32) {
    requires low <= 65535u32;
    requires high <= 65535u32;
    ensures to_integer((high << 16) | low) == to_integer(low) + 65536 * to_integer(high);
}

// Exact round trips of two bounded fields packed with the high field first.
theorem uint32_unpack_uint16_low(low: uint32, high: uint32) {
    requires low <= 65535u32;
    requires high <= 65535u32;
    ensures (((high << 16) | low) & 65535u32) == low;
}

theorem uint32_unpack_uint16_high(low: uint32, high: uint32) {
    requires low <= 65535u32;
    requires high <= 65535u32;
    ensures ((((high << 16) | low) >> 16) & 65535u32) == high;
}

theorem uint64_pack_uint16_to_integer(low: uint64, high: uint64) {
    requires low <= 65535u64;
    requires high <= 65535u64;
    ensures to_integer(low | (high << 16)) == to_integer(low) + 65536 * to_integer(high);
}

// LP64 C saves the same bounded fields in a uint64 result.
theorem uint64_unpack_uint16_low(low: uint64, high: uint64) {
    requires low <= 65535u64;
    requires high <= 65535u64;
    ensures ((low | (high << 16)) & 65535u64) == low;
}

theorem uint64_unpack_uint16_high(low: uint64, high: uint64) {
    requires low <= 65535u64;
    requires high <= 65535u64;
    ensures (((low | (high << 16)) >> 16) & 65535u64) == high;
}

theorem uint64_less_than_implies_not_greater_equal(left: uint64, right: uint64) {
    requires left < right;
    ensures not (left >= right) by close();
}

// Exact observations of unsigned division require both evaluation domains.
theorem uint32_divide_to_integer(left: uint32, right: uint32) {
    requires right != 0u32;
    requires to_integer(right) != 0;
    ensures to_integer(left / right) == truncating_quotient(to_integer(left), to_integer(right));
}

theorem uint32_remainder_to_integer(left: uint32, right: uint32) {
    requires right != 0u32;
    requires to_integer(right) != 0;
    ensures to_integer(left % right) == truncating_remainder(to_integer(left), to_integer(right));
}

theorem uint32_less_equal_to_integer(left: uint32, right: uint32) {
    requires left <= right;
    ensures to_integer(left) <= to_integer(right) by close();
}

theorem uint32_to_integer_less_equal_implies_less_equal(left: uint32, right: uint32) {
    requires to_integer(left) <= to_integer(right);
    ensures left <= right by close();
}

theorem uint32_to_integer_equal_implies_equal(left: uint32, right: uint32) {
    requires to_integer(left) == to_integer(right);
    ensures left == right by close();
}

theorem uint32_to_integer_bounds(value: uint32) {
    ensures 0 <= to_integer(value) by {
        have 0u32 <= value;
        apply(integer::uint32_less_equal_to_integer(0u32, value));
    }
    ensures to_integer(value) <= 4294967295 by {
        have value <= 4294967295u32;
        apply(integer::uint32_less_equal_to_integer(value, 4294967295u32));
    }
}

theorem int32_add_to_integer(left: int32, right: int32) {
    requires defined(left + right);
    ensures to_integer(left + right) == to_integer(left) + to_integer(right) by {
        have -2147483648 <= to_integer(left) + to_integer(right) by {
            close();
        }
        have to_integer(left) + to_integer(right) <= 2147483647 by {
            close();
        }
        have to_integer(left + right) == to_integer(left) + to_integer(right) by {
            close();
        }
        close();
    }
}

theorem int32_less_equal_to_integer(left: int32, right: int32) {
    requires left <= right;
    ensures to_integer(left) <= to_integer(right) by close();
}

theorem int32_to_integer_less_equal_implies_less_equal(left: int32, right: int32) {
    requires to_integer(left) <= to_integer(right);
    ensures left <= right by close();
}

theorem int64_to_integer_less_equal_implies_less_equal(left: int64, right: int64) {
    requires to_integer(left) <= to_integer(right);
    ensures left <= right by close();
}

theorem int32_subtract_to_integer(left: int32, right: int32) {
    requires defined(left - right);
    ensures to_integer(left - right) == to_integer(left) - to_integer(right) by {
        have -2147483648 <= to_integer(left) - to_integer(right) by {
            close();
        }
        have to_integer(left) - to_integer(right) <= 2147483647 by {
            close();
        }
        have to_integer(left - right) == to_integer(left) - to_integer(right) by {
            close();
        }
        close();
    }
}

theorem int32_remainder_to_integer(left: int32, right: int32) {
    requires defined(left % right);
    requires to_integer(right) != 0;
    ensures to_integer(left % right) == truncating_remainder(to_integer(left), to_integer(right));
}

theorem int32_add_defined_by_integer_bounds(left: int32, right: int32) {
    requires to_integer(left) + to_integer(right) >= -2147483648;
    requires to_integer(left) + to_integer(right) <= 2147483647;
    ensures defined(left + right) by {
        close();
    }
}

theorem to_int8_round_trip(z: Integer) {
    requires z >= -128;
    requires z <= 127;
    ensures to_integer(to_int8(z)) == z by {
        have -128 <= z by {
            close();
        }
        have z <= 127 by {
            close();
        }
        close();
    }
}

theorem to_int16_round_trip(z: Integer) {
    requires z >= -32768;
    requires z <= 32767;
    ensures to_integer(to_int16(z)) == z by {
        have -32768 <= z by {
            close();
        }
        have z <= 32767 by {
            close();
        }
        close();
    }
}

theorem to_int32_round_trip(z: Integer) {
    requires z >= -2147483648;
    requires z <= 2147483647;
    ensures to_integer(to_int32(z)) == z by {
        have -2147483648 <= z by {
            close();
        }
        have z <= 2147483647 by {
            close();
        }
        close();
    }
}

theorem to_uint8_round_trip(z: Integer) {
    requires z >= 0;
    requires z <= 255;
    ensures to_integer(to_uint8(z)) == z by {
        have 0 <= z by {
            close();
        }
        have z <= 255 by {
            close();
        }
        close();
    }
}

theorem to_uint16_round_trip(z: Integer) {
    requires z >= 0;
    requires z <= 65535;
    ensures to_integer(to_uint16(z)) == z by {
        have 0 <= z by {
            close();
        }
        have z <= 65535 by {
            close();
        }
        close();
    }
}

theorem to_uint32_round_trip(z: Integer) {
    requires z >= 0;
    requires z <= 4294967295;
    ensures to_integer(to_uint32(z)) == z by {
        have 0 <= z by {
            close();
        }
        have z <= 4294967295 by {
            close();
        }
        close();
    }
}

theorem to_int64_round_trip(z: Integer) {
    requires z >= -9223372036854775808;
    requires z <= 9223372036854775807;
    ensures to_integer(to_int64(z)) == z by {
        have -9223372036854775808 <= z by {
            close();
        }
        have z <= 9223372036854775807 by {
            close();
        }
        close();
    }
}

theorem to_uint64_round_trip(z: Integer) {
    requires z >= 0;
    requires z <= 18446744073709551615;
    ensures to_integer(to_uint64(z)) == z by {
        have 0 <= z by {
            close();
        }
        have z <= 18446744073709551615 by {
            close();
        }
        close();
    }
}

theorem int64_subtract_to_integer(left: int64, right: int64) {
    requires defined(left - right);
    ensures to_integer(left - right) == to_integer(left) - to_integer(right) by {
        have -9223372036854775808 <= to_integer(left) - to_integer(right) by {
            close();
        }
        have to_integer(left) - to_integer(right) <= 9223372036854775807 by {
            close();
        }
        have to_integer(left - right) == to_integer(left) - to_integer(right) by {
            close();
        }
        close();
    }
}

theorem truncation_identity(n: Integer, d: Integer) {
    requires d != 0;
    ensures n == truncating_quotient(n, d) * d + truncating_remainder(n, d);
}

theorem positive_divisor_remainder_lower(n: Integer, d: Integer) {
    requires d != 0;
    requires 0 < d;
    ensures 1 - d <= truncating_remainder(n, d);
}

theorem positive_divisor_remainder_upper(n: Integer, d: Integer) {
    requires d != 0;
    requires 0 < d;
    ensures truncating_remainder(n, d) <= d - 1;
}

theorem nonnegative_dividend_remainder(n: Integer, d: Integer) {
    requires d != 0;
    requires 0 <= n;
    ensures 0 <= truncating_remainder(n, d);
}

theorem nonpositive_dividend_remainder(n: Integer, d: Integer) {
    requires d != 0;
    requires n <= 0;
    ensures truncating_remainder(n, d) <= 0;
}


theorem floor_from_remainder(n: Integer, d: Integer, q: Integer, r: Integer, value: Integer) {
    requires 0 < d;
    requires n == q * d + r;
    requires 1 - d <= r;
    requires r <= d - 1;
    requires r < 0 implies value == q + -1;
    requires 0 <= r implies value == q;
    ensures value * d <= n by {
        if r < 0 {
            have value == q + -1;
            apply(integer::multiply_add(q, -1, d));
            rewrite(value, q + -1);
            rewrite((q + -1) * d, q * d + -1 * d);
            close() using { n == q * d + r; 1 - d <= r; };
        } else {
            have 0 <= r by { close() using { not (r < 0); }; }
            have value == q;
            rewrite(value, q);
            close() using { n == q * d + r; 0 <= r; };
        }
    }
    ensures n < (value + 1) * d by {
        if r < 0 {
            have value == q + -1;
            have value + 1 == q by { close() using { value == q + -1; }; }
            rewrite(value + 1, q);
            close() using { n == q * d + r; r < 0; };
        } else {
            have 0 <= r by { close() using { not (r < 0); }; }
            have value == q;
            apply(integer::multiply_add(q, 1, d));
            rewrite(value, q);
            rewrite((q + 1) * d, q * d + 1 * d);
            close() using { n == q * d + r; r <= d - 1; };
        }
    }
}

theorem ceiling_from_remainder(n: Integer, d: Integer, q: Integer, r: Integer, value: Integer) {
    requires 0 < d;
    requires n == q * d + r;
    requires 1 - d <= r;
    requires r <= d - 1;
    requires 0 < r implies value == q + 1;
    requires r <= 0 implies value == q;
    ensures n <= value * d by {
        if 0 < r {
            have value == q + 1;
            apply(integer::multiply_add(q, 1, d));
            rewrite(value, q + 1);
            rewrite((q + 1) * d, q * d + 1 * d);
            close() using { n == q * d + r; r <= d - 1; };
        } else {
            have r <= 0 by { close() using { not (0 < r); }; }
            have value == q;
            rewrite(value, q);
            close() using { n == q * d + r; r <= 0; };
        }
    }
    ensures (value + -1) * d < n by {
        if 0 < r {
            have value == q + 1;
            have value + -1 == q by { close() using { value == q + 1; }; }
            rewrite(value + -1, q);
            close() using { n == q * d + r; 0 < r; };
        } else {
            have r <= 0 by { close() using { not (0 < r); }; }
            have value == q;
            apply(integer::multiply_add(q, -1, d));
            rewrite(value, q);
            rewrite((q + -1) * d, q * d + -1 * d);
            close() using { n == q * d + r; 1 - d <= r; };
        }
    }
}



theorem le_transitive(a: Integer, b: Integer, c: Integer) {
    requires a <= b;
    requires b <= c;
    ensures a <= c by {
        have a + b <= b + c by {
            apply(integer::add_le(a, b, b, c));
        }
        have (a + b) + -b <= (b + c) + -b by {
            apply(integer::add_le(a + b, b + c, -b, -b));
        }
        have a == (a + b) + -b by { close(); }
        have c == (b + c) + -b by { close(); }
        rewrite(a, (a + b) + -b);
        rewrite(c, (b + c) + -b);
        close();
    }
}

theorem int32_increment_lower_bound(value: int32, lower: int32, upper: int32) {
    requires lower <= value;
    requires value < upper;

    ensures to_integer(lower) <= to_integer(value + 1) by {
        have -2147483648 <= to_integer(value) by close();
        have to_integer(value) <= to_integer(value) + 1 by close();
        have -2147483648 <= to_integer(value) + 1 by {
            apply(integer::le_transitive(-2147483648, to_integer(value), to_integer(value) + 1));
        }
        have to_integer(value) + 1 <= to_integer(upper) by {
            apply(integer::lt_step_le(to_integer(value), to_integer(upper)));
        }
        have to_integer(upper) <= 2147483647 by close();
        have to_integer(value) + 1 <= 2147483647 by {
            apply(integer::le_transitive(to_integer(value) + 1, to_integer(upper), 2147483647));
        }
        have defined(value + 1) by close();
        apply(integer::int32_add_to_integer(value, 1));
        apply(integer::le_transitive(to_integer(lower), to_integer(value), to_integer(value) + 1));
        close();
    }
}

theorem int32_increment_upper_bound(value: int32, upper: int32) {
    requires value < upper;

    ensures to_integer(value + 1) <= to_integer(upper) by {
        have -2147483648 <= to_integer(value) by close();
        have to_integer(value) <= to_integer(value) + 1 by close();
        have -2147483648 <= to_integer(value) + 1 by {
            apply(integer::le_transitive(-2147483648, to_integer(value), to_integer(value) + 1));
        }
        have to_integer(value) + 1 <= to_integer(upper) by {
            apply(integer::lt_step_le(to_integer(value), to_integer(upper)));
        }
        have to_integer(upper) <= 2147483647 by close();
        have to_integer(value) + 1 <= 2147483647 by {
            apply(integer::le_transitive(to_integer(value) + 1, to_integer(upper), 2147483647));
        }
        have defined(value + 1) by close();
        apply(integer::int32_add_to_integer(value, 1));
        close();
    }
}

theorem int32_increment_strictly_increases(value: int32, upper: int32) {
    requires value < upper;

    ensures to_integer(value) < to_integer(value + 1) by {
        have -2147483648 <= to_integer(value) by close();
        have to_integer(value) <= to_integer(value) + 1 by close();
        have -2147483648 <= to_integer(value) + 1 by {
            apply(integer::le_transitive(-2147483648, to_integer(value), to_integer(value) + 1));
        }
        have to_integer(value) + 1 <= to_integer(upper) by {
            apply(integer::lt_step_le(to_integer(value), to_integer(upper)));
        }
        have to_integer(upper) <= 2147483647 by close();
        have to_integer(value) + 1 <= 2147483647 by {
            apply(integer::le_transitive(to_integer(value) + 1, to_integer(upper), 2147483647));
        }
        have defined(value + 1) by close();
        apply(integer::int32_add_to_integer(value, 1));
        have to_integer(value) < to_integer(value) + 1 by close();
        close();
    }
}

theorem int32_increment_below_max_is_defined(value: int32) {
    requires value < 2147483647;

    ensures defined(value + 1) by {
        have -2147483648 <= to_integer(value) by close();
        have to_integer(value) <= to_integer(value) + 1 by close();
        have -2147483648 <= to_integer(value) + 1 by {
            apply(integer::le_transitive(-2147483648, to_integer(value), to_integer(value) + 1));
        }
        have to_integer(value) + 1 <= 2147483647 by {
            apply(integer::lt_step_le(to_integer(value), 2147483647));
        }
        close();
    }
}

theorem uint64_increment_upper_bound(value: uint64, upper: uint64) {
    requires value < upper;
    ensures to_integer(value + 1u64) <= to_integer(upper) by {
        have to_integer(value) < to_integer(upper) by close();
        have (to_integer(value) + 1) <= to_integer(upper) by {
            apply(integer::lt_step_le(to_integer(value), to_integer(upper)));
        }
        have to_integer(upper) <= 18446744073709551615 by close();
        have (to_integer(value) + 1) <= 18446744073709551615 by {
            apply(integer::le_transitive(to_integer(value) + 1, to_integer(upper), 18446744073709551615));
        }
        have (to_integer(value) + to_integer(1u64)) <= 18446744073709551615 by close();
        have to_integer(value + 1u64) == (to_integer(value) + 1) by {
            apply(integer::uint64_add_to_integer(value, 1u64));
            close();
        }
        rewrite(to_integer(value + 1u64), to_integer(value) + 1);
        close();
    }
}

theorem lt_le(a: Integer, b: Integer) {
    requires a < b;
    ensures a <= b by {
        have a + 1 <= b by {
            apply(integer::lt_step_le(a, b));
        }
        have a <= a + 1 by { close(); }
        apply(integer::le_transitive(a, a + 1, b));
    }
}

theorem int32_positive_is_nonnegative(value: int32) {
    requires 0 < value;

    ensures 0 <= value by {
        apply(integer::lt_le(0, to_integer(value)));
        close();
    }
}

theorem add_right_order(a: Integer, b: Integer, c: Integer) {
    requires a <= b;
    ensures a + c <= b + c by {
        apply(integer::add_le(a, b, c, c));
    }
}

theorem int32_less_than_implies_less_equal(first: int32, last: int32) {
    requires first < last;
    ensures first <= last by {
        apply(integer::lt_le(to_integer(first), to_integer(last)));
        close();
    }
}

theorem int32_less_than_less_equal_transitive(first: int32, middle: int32, last: int32) {
    requires first < middle;
    requires middle <= last;
    ensures first < last by {
        have to_integer(first) + 1 <= to_integer(middle) by {
            apply(integer::lt_step_le(to_integer(first), to_integer(middle)));
        }
        have to_integer(first) + 1 <= to_integer(last) by {
            apply(integer::le_transitive(to_integer(first) + 1, to_integer(middle), to_integer(last)));
        }
        apply(integer::step_le_lt(to_integer(first), to_integer(last)));
        close();
    }
}

theorem int32_less_equal_less_than_transitive(first: int32, middle: int32, last: int32) {
    requires first <= middle;
    requires middle < last;

    ensures first < last by {
        have (to_integer(first) + 1) <= (to_integer(middle) + 1) by {
            apply(integer::add_right_order(to_integer(first), to_integer(middle), 1));
        }
        have (to_integer(middle) + 1) <= to_integer(last) by {
            apply(integer::lt_step_le(to_integer(middle), to_integer(last)));
        }
        have (to_integer(first) + 1) <= to_integer(last) by {
            apply(integer::le_transitive(to_integer(first) + 1, to_integer(middle) + 1, to_integer(last)));
        }
        apply(integer::step_le_lt(to_integer(first), to_integer(last)));
        close();
    }
}

theorem int32_less_equal_transitive(first: int32, middle: int32, last: int32) {
    requires first <= middle;
    requires middle <= last;

    ensures first <= last by {
        apply(integer::le_transitive(to_integer(first), to_integer(middle), to_integer(last)));
        close();
    }
}

theorem uint64_less_than_less_equal_transitive(first: uint64, middle: uint64, last: uint64) {
    requires first < middle;
    requires middle <= last;

    ensures first < last by {
        have (to_integer(first) + 1) <= to_integer(middle) by {
            apply(integer::lt_step_le(to_integer(first), to_integer(middle)));
        }
        have (to_integer(first) + 1) <= to_integer(last) by {
            apply(integer::le_transitive(to_integer(first) + 1, to_integer(middle), to_integer(last)));
        }
        apply(integer::step_le_lt(to_integer(first), to_integer(last)));
        close();
    }
}

theorem uint64_less_equal_transitive(first: uint64, middle: uint64, last: uint64) {
    requires first <= middle;
    requires middle <= last;

    ensures first <= last by {
        apply(integer::le_transitive(to_integer(first), to_integer(middle), to_integer(last)));
        close();
    }
}

theorem subtract_right_order(a: Integer, b: Integer, c: Integer) {
    requires a <= b;
    ensures a - c <= b - c by {
        have a + -c <= b + -c by {
            apply(integer::add_right_order(a, b, -c));
        }
        have a - c == a + -c by {
            close();
        }
        have b - c == b + -c by {
            close();
        }
        apply(integer::le_substitute(a + -c, b + -c, a - c, b - c));
    }
}

theorem lt_le_predecessor(a: Integer, b: Integer) {
    requires a < b;
    ensures a <= b - 1 by {
        have a + 1 <= b by {
            apply(integer::lt_step_le(a, b));
        }
        have (a + 1) - 1 <= b - 1 by {
            apply(integer::subtract_right_order(a + 1, b, 1));
        }
        have a == (a + 1) - 1 by { close(); }
        rewrite(a, (a + 1) - 1);
        close();
    }
}

theorem subtract_left_order(a: Integer, b: Integer, c: Integer) {
    requires a <= b;
    ensures c - b <= c - a by {
        have -b <= -a by {
            apply(integer::negate_order(a, b));
        }
        have -b + c <= -a + c by {
            apply(integer::add_right_order(-b, -a, c));
        }
        have c - b == -b + c by {
            close();
        }
        have c - a == -a + c by {
            close();
        }
        apply(integer::le_substitute(-b + c, -a + c, c - b, c - a));
    }
}

theorem int32_positive_predecessor_is_nonnegative(value: int32) {
    requires 0 < value;

    ensures 0 <= to_integer(value - 1) by {
        have 0 <= to_integer(value) - 1 by {
            apply(integer::lt_le_predecessor(0, to_integer(value)));
        }
        have -2147483648 <= to_integer(value) - 1 by {
            apply(integer::le_transitive(-2147483648, 0, to_integer(value) - 1));
        }
        have to_integer(value) - 1 <= to_integer(value) by close();
        have to_integer(value) <= 2147483647 by close();
        have to_integer(value) - 1 <= 2147483647 by {
            apply(integer::le_transitive(to_integer(value) - 1, to_integer(value), 2147483647));
        }
        have defined(value - 1) by close();
        apply(integer::int32_subtract_to_integer(value, 1));
        close();
    }
}

theorem int32_positive_predecessor_strictly_decreases(value: int32) {
    requires 0 < value;

    ensures to_integer(value - 1) < to_integer(value) by {
        have 0 <= to_integer(value) - 1 by {
            apply(integer::lt_le_predecessor(0, to_integer(value)));
        }
        have -2147483648 <= to_integer(value) - 1 by {
            apply(integer::le_transitive(-2147483648, 0, to_integer(value) - 1));
        }
        have to_integer(value) - 1 <= to_integer(value) by close();
        have to_integer(value) <= 2147483647 by close();
        have to_integer(value) - 1 <= 2147483647 by {
            apply(integer::le_transitive(to_integer(value) - 1, to_integer(value), 2147483647));
        }
        have defined(value - 1) by close();
        apply(integer::int32_subtract_to_integer(value, 1));
        have to_integer(value) - 1 < to_integer(value) by close();
        close();
    }
}

theorem int32_nonnegative_predecessor_upper_bound(value: int32, bound: int32) {
    requires 0 <= value;
    requires value <= bound;

    ensures to_integer(value - 1) <= to_integer(bound) by {
        have 0 - 1 <= to_integer(value) - 1 by {
            apply(integer::subtract_right_order(0, to_integer(value), 1));
        }
        have -2147483648 <= to_integer(value) - 1 by {
            apply(integer::le_transitive(-2147483648, 0 - 1, to_integer(value) - 1));
        }
        have to_integer(value) - 1 <= to_integer(value) by close();
        have to_integer(value) <= 2147483647 by close();
        have to_integer(value) - 1 <= 2147483647 by {
            apply(integer::le_transitive(to_integer(value) - 1, to_integer(value), 2147483647));
        }
        have defined(value - 1) by close();
        apply(integer::int32_subtract_to_integer(value, 1));
        apply(integer::le_transitive(to_integer(value) - 1, to_integer(value), to_integer(bound)));
        close();
    }
}

theorem int32_nonnegative_subtract_within_value_is_defined(value: int32, amount: int32) {
    requires 0 <= amount;
    requires amount <= value;

    ensures defined(value - amount) by {
        have to_integer(amount) - to_integer(amount) <= to_integer(value) - to_integer(amount) by {
            apply(integer::subtract_right_order(to_integer(amount), to_integer(value), to_integer(amount)));
        }
        have 0 <= to_integer(value) - to_integer(amount) by {
            have 0 == to_integer(amount) - to_integer(amount) by close();
            rewrite(0, to_integer(amount) - to_integer(amount));
            close();
        }
        have -2147483648 <= to_integer(value) - to_integer(amount) by {
            apply(integer::le_transitive(-2147483648, 0, to_integer(value) - to_integer(amount)));
        }
        have to_integer(value) - to_integer(amount) <= to_integer(value) - 0 by {
            apply(integer::subtract_left_order(0, to_integer(amount), to_integer(value)));
        }
        have to_integer(value) - 0 <= 2147483647 by {
            have to_integer(value) - 0 == to_integer(value) by close();
            rewrite(to_integer(value) - 0, to_integer(value));
            close();
        }
        have to_integer(value) - to_integer(amount) <= 2147483647 by {
            apply(integer::le_transitive(to_integer(value) - to_integer(amount), to_integer(value) - 0, 2147483647));
        }
        close();
    }
}

theorem int32_nonnegative_add_within_max_is_defined(value: int32, amount: int32) {
    requires 0 <= amount;
    requires to_integer(value) <= to_integer(2147483647 - amount);

    ensures defined(value + amount) by {
        have to_integer(amount) <= 2147483647 by close();
        have amount <= 2147483647 by close();
        have defined(2147483647 - amount) by {
            apply(integer::int32_nonnegative_subtract_within_value_is_defined(2147483647, amount));
        }
        apply(integer::int32_subtract_to_integer(2147483647, amount));
        have to_integer(value) <= 2147483647 - to_integer(amount) by {
            rewrite(2147483647 - to_integer(amount), to_integer(2147483647 - amount));
            close();
        }
        have to_integer(value) + to_integer(amount) <= (2147483647 - to_integer(amount)) + to_integer(amount) by {
            apply(integer::add_right_order(to_integer(value), 2147483647 - to_integer(amount), to_integer(amount)));
        }
        have to_integer(value) + to_integer(amount) <= 2147483647 by {
            have 2147483647 == (2147483647 - to_integer(amount)) + to_integer(amount) by close();
            rewrite(2147483647, (2147483647 - to_integer(amount)) + to_integer(amount));
            close();
        }
        have -2147483648 <= to_integer(value) by close();
        have -2147483648 + 0 <= to_integer(value) + to_integer(amount) by {
            apply(integer::add_le(-2147483648, to_integer(value), 0, to_integer(amount)));
        }
        have -2147483648 <= to_integer(value) + to_integer(amount) by {
            have -2147483648 == -2147483648 + 0 by close();
            rewrite(-2147483648, -2147483648 + 0);
            close();
        }
        close();
    }
}

theorem uint32_positive_predecessor_strictly_decreases(value: uint32) {
    requires 0u32 < value;

    ensures to_integer(value - 1u32) < to_integer(value) by {
        have to_integer(0u32) < to_integer(value) by close();
        apply(integer::lt_step_le(0, to_integer(value)));
        have to_integer(1u32) <= to_integer(value) by close();
        have 1u32 <= value by close();
        apply(integer::uint32_subtract_to_integer(value, 1u32));
        have to_integer(value) - 1 < to_integer(value) by close();
        rewrite(to_integer(value - 1u32), to_integer(value) - to_integer(1u32));
        close();
    }
}

theorem uint32_increment_upper_bound(value: uint32, upper: uint32) {
    requires value < upper;

    ensures to_integer(value + 1u32) <= to_integer(upper) by {
        have to_integer(value) + 1 <= to_integer(upper) by {
            apply(integer::lt_step_le(to_integer(value), to_integer(upper)));
        }
        have to_integer(upper) <= 4294967295 by close();
        have to_integer(value) + 1 <= 4294967295 by {
            apply(integer::le_transitive(to_integer(value) + 1, to_integer(upper), 4294967295));
        }
        have to_integer(value) + to_integer(1u32) <= 4294967295 by close();
        apply(integer::uint32_add_to_integer(value, 1u32));
        rewrite(to_integer(value + 1u32), to_integer(value) + to_integer(1u32));
        close();
    }
}

theorem uint32_less_than_implies_positive_difference(value: uint32, upper: uint32) {
    requires value < upper;

    ensures 0 < to_integer(upper - value) by {
        have to_integer(value) + 1 <= to_integer(upper) by {
            apply(integer::lt_step_le(to_integer(value), to_integer(upper)));
        }
        have (to_integer(value) + 1) - to_integer(value) <= to_integer(upper) - to_integer(value) by {
            apply(integer::subtract_right_order(to_integer(value) + 1, to_integer(upper), to_integer(value)));
        }
        have 0 + 1 <= to_integer(upper) - to_integer(value) by {
            have 0 + 1 == (to_integer(value) + 1) - to_integer(value) by close();
            rewrite(0 + 1, (to_integer(value) + 1) - to_integer(value));
            close();
        }
        apply(integer::step_le_lt(0, to_integer(upper) - to_integer(value)));
        have to_integer(value) <= to_integer(upper) by {
            apply(integer::lt_le(to_integer(value), to_integer(upper)));
        }
        have value <= upper by close();
        apply(integer::uint32_subtract_to_integer(upper, value));
        rewrite(to_integer(upper - value), to_integer(upper) - to_integer(value));
        close();
    }
}

theorem subtract_le(a: Integer, b: Integer, c: Integer, d: Integer) {
    requires a <= b;
    requires d <= c;
    ensures a - c <= b - d by {
        have a - c <= b - c by {
            apply(integer::subtract_right_order(a, b, c));
        }
        have b - c <= b - d by {
            apply(integer::subtract_left_order(d, c, b));
        }
        apply(integer::le_transitive(a - c, b - c, b - d));
    }
}

theorem negate_multiply(a: Integer, b: Integer) {
    ensures -a * b == -(a * b) by {
        have b * -a == -(b * a) by {
            apply(integer::multiply_negate(b, a));
        }
        have -a * b == b * -a by {
            apply(integer::multiply_commutative(-a, b));
        }
        have a * b == b * a by {
            apply(integer::multiply_commutative(a, b));
        }
        rewrite(-a * b, b * -a);
        rewrite(a * b, b * a);
        close();
    }
}

theorem sum_commute(a: Integer, b: Integer, c: Integer) {
    requires a == b + c;
    ensures a == c + b by {
        have c + b == b + c by {
            close();
        }
        rewrite(c + b, b + c);
        close();
    }
}

theorem sum_difference(a: Integer, b: Integer, c: Integer) {
    requires a == b + c;
    ensures a + -c == b by {
        have a + -c == (b + c) + -c by {
            apply(integer::equal_add(a, b + c, -c, -c));
        }
        have b == (b + c) + -c by {
            close();
        }
        rewrite(b, (b + c) + -c);
        close();
    }
    ensures -b == -a + c by {
        have a + -c == b by {
            have a + -c == (b + c) + -c by {
                apply(integer::equal_add(a, b + c, -c, -c));
            }
            have b == (b + c) + -c by {
                close();
            }
            rewrite(b, (b + c) + -c);
            close();
        }
        have -(a + -c) == -b by {
            apply(integer::equal_negate(a + -c, b));
        }
        have -a + c == -(a + -c) by {
            close();
        }
        rewrite(-a + c, -(a + -c));
        close();
    }
}

theorem positive_divisor_quotient_lower(n: Integer, d: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires (bound * d) <= n;
    ensures bound <= truncating_quotient(n, d) by {
        have 0 < d by {
            have 0 + 1 <= d by {
                close();
            }
            apply(integer::step_le_lt(0, d));
        }
        have n == (truncating_quotient(n, d) * d) + truncating_remainder(n, d) by {
            apply(integer::truncation_identity(n, d));
        }
        have n + -(truncating_remainder(n, d)) == (truncating_quotient(n, d) * d) by {
            apply(integer::sum_difference(n, (truncating_quotient(n, d) * d), truncating_remainder(n, d)));
        }
        have -(truncating_quotient(n, d) * d) == -n + truncating_remainder(n, d) by {
            apply(integer::sum_difference(n, (truncating_quotient(n, d) * d), truncating_remainder(n, d)));
        }
        have n == truncating_remainder(n, d) + (truncating_quotient(n, d) * d) by {
            apply(integer::sum_commute(n, (truncating_quotient(n, d) * d), truncating_remainder(n, d)));
        }
        have truncating_remainder(n, d) <= (d - 1) by {
            apply(integer::positive_divisor_remainder_upper(n, d));
        }
        have -(d - 1) <= -(truncating_remainder(n, d)) by {
            apply(integer::negate_order(truncating_remainder(n, d), (d - 1)));
        }
        have (bound * d) + -(d - 1) <= n + -(truncating_remainder(n, d)) by {
            apply(integer::add_le((bound * d), n, -(d - 1), -(truncating_remainder(n, d))));
        }
        have (bound * d) - (d - 1) <= (truncating_quotient(n, d) * d) by {
            have (bound * d) - (d - 1) == (bound * d) + -(d - 1) by {
                close();
            }
            have (truncating_quotient(n, d) * d) == n + -(truncating_remainder(n, d)) by {
                close();
            }
            apply(integer::le_substitute((bound * d) + -(d - 1), n + -(truncating_remainder(n, d)), (bound * d) - (d - 1), (truncating_quotient(n, d) * d)));
        }
        have -(truncating_quotient(n, d) * d) <= -((bound * d) - (d - 1)) by {
            apply(integer::negate_order((bound * d) - (d - 1), (truncating_quotient(n, d) * d)));
        }
        have -(truncating_quotient(n, d)) * d == -(truncating_quotient(n, d) * d) by {
            apply(integer::negate_multiply(truncating_quotient(n, d), d));
        }
        have -bound * d == -(bound * d) by {
            apply(integer::negate_multiply(bound, d));
        }
        have -(truncating_quotient(n, d)) * d <= -bound * d + (d - 1) by {
            have -(truncating_quotient(n, d)) * d == -(truncating_quotient(n, d) * d) by {
                rewrite(-(truncating_quotient(n, d)) * d, -(truncating_quotient(n, d) * d));
                close();
            }
            have -bound * d + (d - 1) == -((bound * d) - (d - 1)) by {
                rewrite(-bound * d, -(bound * d));
                close();
            }
            apply(integer::le_substitute(-(truncating_quotient(n, d) * d), -((bound * d) - (d - 1)), -(truncating_quotient(n, d)) * d, -bound * d + (d - 1)));
        }
        have 0 < d by {
            have 0 + 1 <= d by {
                close();
            }
            apply(integer::step_le_lt(0, d));
        }
        have (d - 1) < d by {
            close();
        }
        have -(truncating_quotient(n, d)) <= -bound by {
            apply(integer::round_down_le(-(truncating_quotient(n, d)), -bound, d, (d - 1)));
        }
        have -(-bound) <= -(-(truncating_quotient(n, d))) by {
            apply(integer::negate_order(-(truncating_quotient(n, d)), -bound));
        }
        have bound == -(-bound) by {
            close();
        }
        have truncating_quotient(n, d) == -(-(truncating_quotient(n, d))) by {
            close();
        }
        apply(integer::le_substitute(-(-bound), -(-(truncating_quotient(n, d))), bound, truncating_quotient(n, d)));
    }
}

theorem positive_divisor_quotient_upper(n: Integer, d: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires n <= (bound * d);
    ensures truncating_quotient(n, d) <= bound by {
        have 0 < d by {
            have 0 + 1 <= d by {
                close();
            }
            apply(integer::step_le_lt(0, d));
        }
        have n == (truncating_quotient(n, d) * d) + truncating_remainder(n, d) by {
            apply(integer::truncation_identity(n, d));
        }
        have n + -(truncating_remainder(n, d)) == (truncating_quotient(n, d) * d) by {
            apply(integer::sum_difference(n, (truncating_quotient(n, d) * d), truncating_remainder(n, d)));
        }
        have -(truncating_quotient(n, d) * d) == -n + truncating_remainder(n, d) by {
            apply(integer::sum_difference(n, (truncating_quotient(n, d) * d), truncating_remainder(n, d)));
        }
        have n == truncating_remainder(n, d) + (truncating_quotient(n, d) * d) by {
            apply(integer::sum_commute(n, (truncating_quotient(n, d) * d), truncating_remainder(n, d)));
        }
        have 1 - d <= truncating_remainder(n, d) by {
            apply(integer::positive_divisor_remainder_lower(n, d));
        }
        have -(truncating_remainder(n, d)) <= (d - 1) by {
            have -(truncating_remainder(n, d)) <= -(1 - d) by {
                apply(integer::negate_order(1 - d, truncating_remainder(n, d)));
            }
            have -(truncating_remainder(n, d)) == -(truncating_remainder(n, d)) by {
                close();
            }
            have (d - 1) == -(1 - d) by {
                close();
            }
            apply(integer::le_substitute(-(truncating_remainder(n, d)), -(1 - d), -(truncating_remainder(n, d)), (d - 1)));
        }
        have n + -(truncating_remainder(n, d)) <= (bound * d) + (d - 1) by {
            apply(integer::add_le(n, (bound * d), -(truncating_remainder(n, d)), (d - 1)));
        }
        have (truncating_quotient(n, d) * d) <= (bound * d) + (d - 1) by {
            have (truncating_quotient(n, d) * d) == n + -(truncating_remainder(n, d)) by {
                close();
            }
            have (bound * d) + (d - 1) == (bound * d) + (d - 1) by {
                close();
            }
            apply(integer::le_substitute(n + -(truncating_remainder(n, d)), (bound * d) + (d - 1), (truncating_quotient(n, d) * d), (bound * d) + (d - 1)));
        }
        have 0 < d by {
            have 0 + 1 <= d by {
                close();
            }
            apply(integer::step_le_lt(0, d));
        }
        have (d - 1) < d by {
            close();
        }
        apply(integer::round_down_le(truncating_quotient(n, d), bound, d, (d - 1)));
    }
}

theorem positive_divisor_quotient_strict_lower(n: Integer, d: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires bound < 0;
    requires bound * d < n;
    ensures bound < truncating_quotient(n, d) by {
        have bound * d <= n by { close() using { bound * d < n; }; }
        apply(integer::positive_divisor_quotient_lower(n, d, bound));
        if bound < truncating_quotient(n, d) {
            close();
        } else {
            have truncating_quotient(n, d) == bound by { close() using {
                bound <= truncating_quotient(n, d); not (bound < truncating_quotient(n, d));
            }; }
            if n <= 0 {
                have 0 < d by { close() using { 1 <= d; }; }
                apply(integer::nonpositive_dividend_remainder(n, d));
                apply(integer::truncation_identity(n, d));
                have n == bound * d + truncating_remainder(n, d) by {
                    rewrite(bound, truncating_quotient(n, d));
                    close();
                }
                have not (bound * d < n) by { close() using {
                    n == bound * d + truncating_remainder(n, d); truncating_remainder(n, d) <= 0;
                }; }
                contradiction(bound * d < n);
            } else {
                have 0 <= n by { close() using { not (n <= 0); }; }
                have 0 * d <= n by { close() using { 0 <= n; }; }
                apply(integer::positive_divisor_quotient_lower(n, d, 0));
                have not (bound < 0) by { close() using {
                    0 <= truncating_quotient(n, d); truncating_quotient(n, d) == bound;
                }; }
                contradiction(bound < 0);
            }
        }
    }
}

theorem positive_divisor_quotient_strict_upper(n: Integer, d: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires 0 < bound;
    requires n < bound * d;
    ensures truncating_quotient(n, d) < bound by {
        have n <= bound * d by { close() using { n < bound * d; }; }
        apply(integer::positive_divisor_quotient_upper(n, d, bound));
        if truncating_quotient(n, d) < bound {
            close();
        } else {
            have truncating_quotient(n, d) == bound by { close() using {
                truncating_quotient(n, d) <= bound; not (truncating_quotient(n, d) < bound);
            }; }
            if 0 <= n {
                have 0 < d by { close() using { 1 <= d; }; }
                apply(integer::nonnegative_dividend_remainder(n, d));
                apply(integer::truncation_identity(n, d));
                have n == bound * d + truncating_remainder(n, d) by {
                    rewrite(bound, truncating_quotient(n, d));
                    close();
                }
                have not (n < bound * d) by { close() using {
                    n == bound * d + truncating_remainder(n, d); 0 <= truncating_remainder(n, d);
                }; }
                contradiction(n < bound * d);
            } else {
                have n <= 0 by { close() using { not (0 <= n); }; }
                have n <= 0 * d by { close() using { n <= 0; }; }
                apply(integer::positive_divisor_quotient_upper(n, d, 0));
                have not (0 < bound) by { close() using {
                    truncating_quotient(n, d) <= 0; truncating_quotient(n, d) == bound;
                }; }
                contradiction(0 < bound);
            }
        }
    }
}

theorem lower_correction_bound(n: Integer, d: Integer, q: Integer, r: Integer, lower: Integer) {
    requires lower <= q;
    requires lower * d <= n;
    requires n == q * d + r;
    requires r < 0;
    ensures lower + 1 <= q by {
        if lower + 1 <= q {
            close();
        } else {
            have q == lower by { close() using { lower <= q; not (lower + 1 <= q); }; }
            have n == lower * d + r by {
                rewrite(lower, q);
                close();
            }
            have not (r < 0) by { close() using { lower * d <= n; n == lower * d + r; }; }
            contradiction(r < 0);
        }
    }
}

theorem upper_correction_bound(n: Integer, d: Integer, q: Integer, r: Integer, upper: Integer) {
    requires q <= upper;
    requires n <= upper * d;
    requires n == q * d + r;
    requires 0 < r;
    ensures q <= upper + -1 by {
        if q <= upper + -1 {
            close();
        } else {
            have q == upper by { close() using { q <= upper; not (q <= upper + -1); }; }
            have n == upper * d + r by {
                rewrite(upper, q);
                close();
            }
            have not (0 < r) by { close() using { n <= upper * d; n == upper * d + r; }; }
            contradiction(0 < r);
        }
    }
}


// Elementary multiplication equations, named separately from order reasoning.





theorem multiply_order_nonpositive(a: Integer, b: Integer, factor: Integer) {
    requires a <= b;
    requires factor <= 0;
    ensures b * factor <= a * factor by {
        have 0 <= -factor by {
            have factor + -factor <= 0 + -factor by {
                apply(integer::add_le(factor, 0, -factor, -factor));
            }
            have 0 == factor + -factor by { close(); }
            have -factor == 0 + -factor by { close(); }
            rewrite(0, factor + -factor);
            rewrite(-factor, 0 + -factor);
            close();
        }
        have a * -factor <= b * -factor by {
            apply(integer::multiply_order_nonnegative(a, b, -factor));
        }
        have -(b * -factor) <= -(a * -factor) by {
            apply(integer::negate_order(a * -factor, b * -factor));
        }
        have b * -factor == -(b * factor) by { apply(integer::multiply_negate(b, factor)); }
        have a * -factor == -(a * factor) by { apply(integer::multiply_negate(a, factor)); }
        have b * factor == -(-(b * factor)) by { close(); }
        have a * factor == -(-(a * factor)) by { close(); }
        rewrite(b * factor, -(-(b * factor)));
        rewrite(a * factor, -(-(a * factor)));
        rewrite(-(b * factor), b * -factor);
        rewrite(-(a * factor), a * -factor);
        close();
    }
}

theorem scaled_product_bounds(value: Integer, amount: Integer, size: Integer, lower: Integer, upper: Integer) {
    requires lower <= value;
    requires value <= upper;
    requires lower <= 0;
    requires 0 <= upper;
    requires 0 <= amount;
    requires amount <= size;
    ensures lower * size <= value * amount by {
        have lower * amount <= value * amount by {
            apply(integer::multiply_order_nonnegative(lower, value, amount));
        }
        have size * lower <= amount * lower by {
            apply(integer::multiply_order_nonpositive(amount, size, lower));
        }
        have lower * size == size * lower by { apply(integer::multiply_commutative(lower, size)); }
        have lower * amount == amount * lower by { apply(integer::multiply_commutative(lower, amount)); }
        have lower * size <= lower * amount by {
            rewrite(lower * size, size * lower);
            rewrite(lower * amount, amount * lower);
            close();
        }
        apply(integer::le_transitive(lower * size, lower * amount, value * amount));
    }
    ensures value * amount <= upper * size by {
        have value * amount <= upper * amount by {
            apply(integer::multiply_order_nonnegative(value, upper, amount));
        }
        have amount * upper <= size * upper by {
            apply(integer::multiply_order_nonnegative(amount, size, upper));
        }
        have upper * amount == amount * upper by { apply(integer::multiply_commutative(upper, amount)); }
        have upper * size == size * upper by { apply(integer::multiply_commutative(upper, size)); }
        have upper * amount <= upper * size by {
            rewrite(upper * amount, amount * upper);
            rewrite(upper * size, size * upper);
            close();
        }
        apply(integer::le_transitive(value * amount, upper * amount, upper * size));
    }
}

theorem product_lower_bound(x: Integer, y: Integer, lo_x: Integer, hi_x: Integer, lo_y: Integer, hi_y: Integer, bound: Integer) {
    requires lo_x <= x;
    requires x <= hi_x;
    requires lo_y <= y;
    requires y <= hi_y;
    requires bound <= lo_x * lo_y;
    requires bound <= lo_x * hi_y;
    requires bound <= hi_x * lo_y;
    requires bound <= hi_x * hi_y;
    ensures bound <= x * y by {
        have x * y == y * x by { apply(integer::multiply_commutative(x, y)); }
        if 0 <= x {
            have lo_y * x <= y * x by {
                apply(integer::multiply_order_nonnegative(lo_y, y, x));
            }
            if 0 <= lo_y {
                have lo_x * lo_y <= x * lo_y by {
                    apply(integer::multiply_order_nonnegative(lo_x, x, lo_y));
                }
                have x * lo_y == lo_y * x by { apply(integer::multiply_commutative(x, lo_y)); }
                have bound <= lo_y * x by {
                    rewrite(lo_y * x, x * lo_y);
                    apply(integer::le_transitive(bound, lo_x * lo_y, x * lo_y));
                }
                rewrite(x * y, y * x);
                apply(integer::le_transitive(bound, lo_y * x, y * x));
            } else {
                have lo_y < 0 by { close(); }
                have lo_y <= 0 by {
                    apply(integer::lt_le(lo_y, 0));
                }
                have hi_x * lo_y <= x * lo_y by {
                    apply(integer::multiply_order_nonpositive(x, hi_x, lo_y));
                }
                have x * lo_y == lo_y * x by { apply(integer::multiply_commutative(x, lo_y)); }
                have bound <= lo_y * x by {
                    rewrite(lo_y * x, x * lo_y);
                    apply(integer::le_transitive(bound, hi_x * lo_y, x * lo_y));
                }
                rewrite(x * y, y * x);
                apply(integer::le_transitive(bound, lo_y * x, y * x));
            }
        } else {
            have x < 0 by { close(); }
                have x <= 0 by {
                    apply(integer::lt_le(x, 0));
                }
            have hi_y * x <= y * x by {
                apply(integer::multiply_order_nonpositive(y, hi_y, x));
            }
            if 0 <= hi_y {
                have lo_x * hi_y <= x * hi_y by {
                    apply(integer::multiply_order_nonnegative(lo_x, x, hi_y));
                }
                have x * hi_y == hi_y * x by { apply(integer::multiply_commutative(x, hi_y)); }
                have bound <= hi_y * x by {
                    rewrite(hi_y * x, x * hi_y);
                    apply(integer::le_transitive(bound, lo_x * hi_y, x * hi_y));
                }
                rewrite(x * y, y * x);
                apply(integer::le_transitive(bound, hi_y * x, y * x));
            } else {
                have hi_y < 0 by { close(); }
                have hi_y <= 0 by {
                    apply(integer::lt_le(hi_y, 0));
                }
                have hi_x * hi_y <= x * hi_y by {
                    apply(integer::multiply_order_nonpositive(x, hi_x, hi_y));
                }
                have x * hi_y == hi_y * x by { apply(integer::multiply_commutative(x, hi_y)); }
                have bound <= hi_y * x by {
                    rewrite(hi_y * x, x * hi_y);
                    apply(integer::le_transitive(bound, hi_x * hi_y, x * hi_y));
                }
                rewrite(x * y, y * x);
                apply(integer::le_transitive(bound, hi_y * x, y * x));
            }
        }
    }
}

theorem product_upper_bound(x: Integer, y: Integer, lo_x: Integer, hi_x: Integer, lo_y: Integer, hi_y: Integer, bound: Integer) {
    requires lo_x <= x;
    requires x <= hi_x;
    requires lo_y <= y;
    requires y <= hi_y;
    requires lo_x * lo_y <= bound;
    requires lo_x * hi_y <= bound;
    requires hi_x * lo_y <= bound;
    requires hi_x * hi_y <= bound;
    ensures x * y <= bound by {
        have x * y == y * x by { apply(integer::multiply_commutative(x, y)); }
        if 0 <= x {
            have y * x <= hi_y * x by {
                apply(integer::multiply_order_nonnegative(y, hi_y, x));
            }
            if 0 <= hi_y {
                have x * hi_y <= hi_x * hi_y by {
                    apply(integer::multiply_order_nonnegative(x, hi_x, hi_y));
                }
                have x * hi_y == hi_y * x by { apply(integer::multiply_commutative(x, hi_y)); }
                have hi_y * x <= bound by {
                    rewrite(hi_y * x, x * hi_y);
                    apply(integer::le_transitive(x * hi_y, hi_x * hi_y, bound));
                }
                rewrite(x * y, y * x);
                apply(integer::le_transitive(y * x, hi_y * x, bound));
            } else {
                have hi_y < 0 by { close(); }
                have hi_y <= 0 by {
                    apply(integer::lt_le(hi_y, 0));
                }
                have x * hi_y <= lo_x * hi_y by {
                    apply(integer::multiply_order_nonpositive(lo_x, x, hi_y));
                }
                have x * hi_y == hi_y * x by { apply(integer::multiply_commutative(x, hi_y)); }
                have hi_y * x <= bound by {
                    rewrite(hi_y * x, x * hi_y);
                    apply(integer::le_transitive(x * hi_y, lo_x * hi_y, bound));
                }
                rewrite(x * y, y * x);
                apply(integer::le_transitive(y * x, hi_y * x, bound));
            }
        } else {
            have x < 0 by { close(); }
                have x <= 0 by {
                    apply(integer::lt_le(x, 0));
                }
            have y * x <= lo_y * x by {
                apply(integer::multiply_order_nonpositive(lo_y, y, x));
            }
            if 0 <= lo_y {
                have x * lo_y <= hi_x * lo_y by {
                    apply(integer::multiply_order_nonnegative(x, hi_x, lo_y));
                }
                have x * lo_y == lo_y * x by { apply(integer::multiply_commutative(x, lo_y)); }
                have lo_y * x <= bound by {
                    rewrite(lo_y * x, x * lo_y);
                    apply(integer::le_transitive(x * lo_y, hi_x * lo_y, bound));
                }
                rewrite(x * y, y * x);
                apply(integer::le_transitive(y * x, lo_y * x, bound));
            } else {
                have lo_y < 0 by { close(); }
                have lo_y <= 0 by {
                    apply(integer::lt_le(lo_y, 0));
                }
                have x * lo_y <= lo_x * lo_y by {
                    apply(integer::multiply_order_nonpositive(lo_x, x, lo_y));
                }
                have x * lo_y == lo_y * x by { apply(integer::multiply_commutative(x, lo_y)); }
                have lo_y * x <= bound by {
                    rewrite(lo_y * x, x * lo_y);
                    apply(integer::le_transitive(x * lo_y, lo_x * lo_y, bound));
                }
                rewrite(x * y, y * x);
                apply(integer::le_transitive(y * x, lo_y * x, bound));
            }
        }
    }
}

// Unsigned 32-bit product and remainder laws, proved from the division
// observations and the truncating-division lemmas above.
theorem uint32_multiply_to_integer(left: uint32, right: uint32) {
    requires right == 0u32 or left <= 4294967295u32 / right;
    ensures to_integer(left * right) == to_integer(left) * to_integer(right) by {
        have 0 <= to_integer(left) by close();
        have 0 <= to_integer(right) by close();
        have 0 * to_integer(right) <= (to_integer(left) * to_integer(right)) by {
            apply(integer::multiply_order_nonnegative(0, to_integer(left), to_integer(right)));
        }
        have 0 <= (to_integer(left) * to_integer(right)) by close();
        if right == 0u32 {
            have to_integer(right) == 0 by close();
            have (to_integer(left) * to_integer(right)) == 0 by {
                rewrite(to_integer(right), 0);
                close();
            }
            have (to_integer(left) * to_integer(right)) <= 4294967295 by {
                apply(integer::le_substitute(0, 4294967295, (to_integer(left) * to_integer(right)), 4294967295));
            }
            close();
        } else {
            have to_integer(right) != 0 by close();
            have to_integer(left) <= to_integer(4294967295u32 / right) by {
                cases {
                    right == 0u32 => { contradiction(right == 0u32); }
                    to_integer(left) <= to_integer(4294967295u32 / right) => { close(); }
                }
            }
            have to_integer(4294967295u32 / right) == truncating_quotient(4294967295, to_integer(right)) by {
                apply(integer::uint32_divide_to_integer(4294967295u32, right));
            }
            have to_integer(left) <= truncating_quotient(4294967295, to_integer(right)) by {
                rewrite(truncating_quotient(4294967295, to_integer(right)), to_integer(4294967295u32 / right));
                close();
            }
            have 4294967295 == (truncating_quotient(4294967295, to_integer(right)) * to_integer(right)) + truncating_remainder(4294967295, to_integer(right)) by {
                apply(integer::truncation_identity(4294967295, to_integer(right)));
            }
            have 0 <= truncating_remainder(4294967295, to_integer(right)) by {
                apply(integer::nonnegative_dividend_remainder(4294967295, to_integer(right)));
            }
            have (truncating_quotient(4294967295, to_integer(right)) * to_integer(right)) + 0 <= (truncating_quotient(4294967295, to_integer(right)) * to_integer(right)) + truncating_remainder(4294967295, to_integer(right)) by {
                apply(integer::add_le((truncating_quotient(4294967295, to_integer(right)) * to_integer(right)), (truncating_quotient(4294967295, to_integer(right)) * to_integer(right)), 0, truncating_remainder(4294967295, to_integer(right))));
            }
            have (truncating_quotient(4294967295, to_integer(right)) * to_integer(right)) == (truncating_quotient(4294967295, to_integer(right)) * to_integer(right)) + 0 by close();
            have (truncating_quotient(4294967295, to_integer(right)) * to_integer(right)) <= 4294967295 by {
                apply(integer::le_substitute((truncating_quotient(4294967295, to_integer(right)) * to_integer(right)) + 0, (truncating_quotient(4294967295, to_integer(right)) * to_integer(right)) + truncating_remainder(4294967295, to_integer(right)), (truncating_quotient(4294967295, to_integer(right)) * to_integer(right)), 4294967295));
            }
            have (to_integer(left) * to_integer(right)) <= (truncating_quotient(4294967295, to_integer(right)) * to_integer(right)) by {
                apply(integer::multiply_order_nonnegative(to_integer(left), truncating_quotient(4294967295, to_integer(right)), to_integer(right)));
            }
            have (to_integer(left) * to_integer(right)) <= 4294967295 by {
                apply(integer::le_transitive((to_integer(left) * to_integer(right)), (truncating_quotient(4294967295, to_integer(right)) * to_integer(right)), 4294967295));
            }
            close();
        }
    }
}

theorem uint32_multiply_guard_by_integer_bound(left: uint32, right: uint32) {
    requires to_integer(left) * to_integer(right) <= 4294967295;
    ensures right == 0u32 or left <= 4294967295u32 / right by {
        if right != 0u32 {
            have to_integer(right) != 0 by close();
            have 0 <= to_integer(right) by close();
            have 0 < to_integer(right) by {
                apply(integer::le_ne_lt(0, to_integer(right)));
            }
            apply(integer::lt_step_le(0, to_integer(right)));
            have 1 <= to_integer(right) by close();
            apply(integer::positive_divisor_quotient_lower(4294967295, to_integer(right), to_integer(left)));
            apply(integer::uint32_divide_to_integer(4294967295u32, right));
            have to_integer(left) <= to_integer(4294967295u32 / right) by {
                rewrite(to_integer(4294967295u32 / right), truncating_quotient(4294967295, to_integer(right)));
                close();
            }
            have left <= 4294967295u32 / right by close();
            close();
        } else {
            have right == 0u32 by close();
            close();
        }
    }
}

theorem uint32_remainder_less_than_divisor(value: uint32, divisor: uint32) {
    requires divisor != 0u32;
    ensures value % divisor < divisor by {
        have to_integer(divisor) != 0 by close();
        have 0 <= to_integer(divisor) by close();
        have 0 < to_integer(divisor) by {
            apply(integer::le_ne_lt(0, to_integer(divisor)));
        }
        apply(integer::uint32_remainder_to_integer(value, divisor));
        apply(integer::positive_divisor_remainder_upper(to_integer(value), to_integer(divisor)));
        have truncating_remainder(to_integer(value), to_integer(divisor)) + 1 <= (to_integer(divisor) - 1) + 1 by {
            apply(integer::add_le(truncating_remainder(to_integer(value), to_integer(divisor)), to_integer(divisor) - 1, 1, 1));
        }
        have truncating_remainder(to_integer(value), to_integer(divisor)) + 1 <= to_integer(divisor) by {
            have to_integer(divisor) == (to_integer(divisor) - 1) + 1 by close();
            apply(integer::le_substitute(truncating_remainder(to_integer(value), to_integer(divisor)) + 1, (to_integer(divisor) - 1) + 1, truncating_remainder(to_integer(value), to_integer(divisor)) + 1, to_integer(divisor)));
        }
        have to_integer(value % divisor) + 1 == truncating_remainder(to_integer(value), to_integer(divisor)) + 1 by {
            apply(integer::equal_add(to_integer(value % divisor), truncating_remainder(to_integer(value), to_integer(divisor)), 1, 1));
        }
        have to_integer(value % divisor) + 1 <= to_integer(divisor) by {
            apply(integer::le_substitute(truncating_remainder(to_integer(value), to_integer(divisor)) + 1, to_integer(divisor), to_integer(value % divisor) + 1, to_integer(divisor)));
        }
        apply(integer::step_le_lt(to_integer(value % divisor), to_integer(divisor)));
    }
}

// A native nonzero quotient guard bounds the exact Integer product.
theorem uint64_product_bound_from_division(x: uint64, y: uint64) {
    requires y != 0u64;
    requires x <= 18446744073709551615u64 / y;
    ensures to_integer(x) * to_integer(y) <= to_integer(18446744073709551615u64) by {
        have to_integer(y) != 0;
        have 0 <= to_integer(y);
        have 0 <= to_integer(18446744073709551615u64) by close();
        apply(integer::uint64_divide_to_integer(18446744073709551615u64, y));
        have to_integer(x) <= to_integer(18446744073709551615u64 / y);
        apply(integer::multiply_order_nonnegative(to_integer(x), to_integer(18446744073709551615u64 / y), to_integer(y)));
        apply(integer::truncation_identity(to_integer(18446744073709551615u64), to_integer(y)));
        apply(integer::nonnegative_dividend_remainder(to_integer(18446744073709551615u64), to_integer(y)));
        have to_integer(18446744073709551615u64 / y) * to_integer(y) == truncating_quotient(to_integer(18446744073709551615u64), to_integer(y)) * to_integer(y) by {
            rewrite(to_integer(18446744073709551615u64 / y), truncating_quotient(to_integer(18446744073709551615u64), to_integer(y)));
            close();
        }
        close() using {
            to_integer(x) * to_integer(y) <= to_integer(18446744073709551615u64 / y) * to_integer(y);
            to_integer(18446744073709551615u64 / y) * to_integer(y) == truncating_quotient(to_integer(18446744073709551615u64), to_integer(y)) * to_integer(y);
            to_integer(18446744073709551615u64) == truncating_quotient(to_integer(18446744073709551615u64), to_integer(y)) * to_integer(y) + truncating_remainder(to_integer(18446744073709551615u64), to_integer(y));
            0 <= truncating_remainder(to_integer(18446744073709551615u64), to_integer(y));
        };
    }
}

// Representation bytes of one readable unsigned word, at the current point.
theorem uint32_from_le_bytes(p: uint32*) {
    requires little_endian();
    views p[0..1];
    requires defined(p[0]);
    ensures p[0] ==
        (((p as (uint8 *))[0] as uint32) |
         ((p as (uint8 *))[1] as uint32) << 8u32 |
         ((p as (uint8 *))[2] as uint32) << 16u32 |
         ((p as (uint8 *))[3] as uint32) << 24u32);
}

// Ordinary proofs for explicit quotient and remainder interval bounds.











theorem positive_divisor_quotient_upper_rounded(n: Integer, d: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires 0 <= n;
    requires n <= (bound * d) + (d - 1);
    ensures truncating_quotient(n, d) <= bound by {
        have n == (truncating_quotient(n, d) * d) + truncating_remainder(n, d) by {
            apply(integer::truncation_identity(n, d));
        }
        have n + -(truncating_remainder(n, d)) == (truncating_quotient(n, d) * d) by {
            apply(integer::sum_difference(n, (truncating_quotient(n, d) * d), truncating_remainder(n, d)));
        }
        have -(truncating_quotient(n, d) * d) == -n + truncating_remainder(n, d) by {
            apply(integer::sum_difference(n, (truncating_quotient(n, d) * d), truncating_remainder(n, d)));
        }
        have n == truncating_remainder(n, d) + (truncating_quotient(n, d) * d) by {
            apply(integer::sum_commute(n, (truncating_quotient(n, d) * d), truncating_remainder(n, d)));
        }
        have 0 <= truncating_remainder(n, d) by {
            apply(integer::nonnegative_dividend_remainder(n, d));
        }
        have 0 + (truncating_quotient(n, d) * d) <= truncating_remainder(n, d) + (truncating_quotient(n, d) * d) by {
            apply(integer::add_le(0, truncating_remainder(n, d), (truncating_quotient(n, d) * d), (truncating_quotient(n, d) * d)));
        }
        have (truncating_quotient(n, d) * d) <= n by {
            have (truncating_quotient(n, d) * d) == 0 + (truncating_quotient(n, d) * d) by {
                close();
            }
            have n == truncating_remainder(n, d) + (truncating_quotient(n, d) * d) by {
                close();
            }
            apply(integer::le_substitute(0 + (truncating_quotient(n, d) * d), truncating_remainder(n, d) + (truncating_quotient(n, d) * d), (truncating_quotient(n, d) * d), n));
        }
        have (truncating_quotient(n, d) * d) <= (bound * d) + (d - 1) by {
            apply(integer::le_transitive((truncating_quotient(n, d) * d), n, (bound * d) + (d - 1)));
        }
        have 0 < d by {
            have 0 + 1 <= d by {
                close();
            }
            apply(integer::step_le_lt(0, d));
        }
        have (d - 1) < d by {
            close();
        }
        apply(integer::round_down_le(truncating_quotient(n, d), bound, d, (d - 1)));
    }
}

theorem positive_divisor_quotient_lower_rounded(n: Integer, d: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires n <= 0;
    requires (bound * d) - (d - 1) <= n;
    ensures bound <= truncating_quotient(n, d) by {
        have n == (truncating_quotient(n, d) * d) + truncating_remainder(n, d) by {
            apply(integer::truncation_identity(n, d));
        }
        have n + -(truncating_remainder(n, d)) == (truncating_quotient(n, d) * d) by {
            apply(integer::sum_difference(n, (truncating_quotient(n, d) * d), truncating_remainder(n, d)));
        }
        have -(truncating_quotient(n, d) * d) == -n + truncating_remainder(n, d) by {
            apply(integer::sum_difference(n, (truncating_quotient(n, d) * d), truncating_remainder(n, d)));
        }
        have n == truncating_remainder(n, d) + (truncating_quotient(n, d) * d) by {
            apply(integer::sum_commute(n, (truncating_quotient(n, d) * d), truncating_remainder(n, d)));
        }
        have truncating_remainder(n, d) <= 0 by {
            apply(integer::nonpositive_dividend_remainder(n, d));
        }
        have truncating_remainder(n, d) + (truncating_quotient(n, d) * d) <= 0 + (truncating_quotient(n, d) * d) by {
            apply(integer::add_le(truncating_remainder(n, d), 0, (truncating_quotient(n, d) * d), (truncating_quotient(n, d) * d)));
        }
        have n <= (truncating_quotient(n, d) * d) by {
            have n == truncating_remainder(n, d) + (truncating_quotient(n, d) * d) by {
                close();
            }
            have (truncating_quotient(n, d) * d) == 0 + (truncating_quotient(n, d) * d) by {
                close();
            }
            apply(integer::le_substitute(truncating_remainder(n, d) + (truncating_quotient(n, d) * d), 0 + (truncating_quotient(n, d) * d), n, (truncating_quotient(n, d) * d)));
        }
        have (bound * d) - (d - 1) <= (truncating_quotient(n, d) * d) by {
            apply(integer::le_transitive((bound * d) - (d - 1), n, (truncating_quotient(n, d) * d)));
        }
        have -(truncating_quotient(n, d) * d) <= -((bound * d) - (d - 1)) by {
            apply(integer::negate_order((bound * d) - (d - 1), (truncating_quotient(n, d) * d)));
        }
        have -(truncating_quotient(n, d)) * d == -(truncating_quotient(n, d) * d) by {
            apply(integer::negate_multiply(truncating_quotient(n, d), d));
        }
        have -bound * d == -(bound * d) by {
            apply(integer::negate_multiply(bound, d));
        }
        have -(truncating_quotient(n, d)) * d <= -bound * d + (d - 1) by {
            have -(truncating_quotient(n, d)) * d == -(truncating_quotient(n, d) * d) by {
                rewrite(-(truncating_quotient(n, d)) * d, -(truncating_quotient(n, d) * d));
                close();
            }
            have -bound * d + (d - 1) == -((bound * d) - (d - 1)) by {
                rewrite(-bound * d, -(bound * d));
                close();
            }
            apply(integer::le_substitute(-(truncating_quotient(n, d) * d), -((bound * d) - (d - 1)), -(truncating_quotient(n, d)) * d, -bound * d + (d - 1)));
        }
        have 0 < d by {
            have 0 + 1 <= d by {
                close();
            }
            apply(integer::step_le_lt(0, d));
        }
        have (d - 1) < d by {
            close();
        }
        have -(truncating_quotient(n, d)) <= -bound by {
            apply(integer::round_down_le(-(truncating_quotient(n, d)), -bound, d, (d - 1)));
        }
        have -(-bound) <= -(-(truncating_quotient(n, d))) by {
            apply(integer::negate_order(-(truncating_quotient(n, d)), -bound));
        }
        have bound == -(-bound) by {
            close();
        }
        have truncating_quotient(n, d) == -(-(truncating_quotient(n, d))) by {
            close();
        }
        apply(integer::le_substitute(-(-bound), -(-(truncating_quotient(n, d))), bound, truncating_quotient(n, d)));
    }
}

theorem nonnegative_dividend_remainder_upper(n: Integer, d: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires 0 <= n;
    ensures truncating_remainder(n, d) <= n by {
        have 0 < d by {
            have 0 + 1 <= d by {
                close();
            }
            apply(integer::step_le_lt(0, d));
        }
        have 0 <= d by {
            apply(integer::lt_le(0, d));
        }
        have n == (truncating_quotient(n, d) * d) + truncating_remainder(n, d) by {
            apply(integer::truncation_identity(n, d));
        }
        have n + -(truncating_remainder(n, d)) == (truncating_quotient(n, d) * d) by {
            apply(integer::sum_difference(n, (truncating_quotient(n, d) * d), truncating_remainder(n, d)));
        }
        have -(truncating_quotient(n, d) * d) == -n + truncating_remainder(n, d) by {
            apply(integer::sum_difference(n, (truncating_quotient(n, d) * d), truncating_remainder(n, d)));
        }
        have n == truncating_remainder(n, d) + (truncating_quotient(n, d) * d) by {
            apply(integer::sum_commute(n, (truncating_quotient(n, d) * d), truncating_remainder(n, d)));
        }
        have 0 * d == 0 by {
            close();
        }
        have 0 * d <= n by {
            rewrite(0 * d, 0);
            close();
        }
        have 0 <= truncating_quotient(n, d) by {
            apply(integer::positive_divisor_quotient_lower(n, d, 0));
        }
        have 0 * d <= (truncating_quotient(n, d) * d) by {
            apply(integer::multiply_order_nonnegative(0, truncating_quotient(n, d), d));
        }
        have 0 <= (truncating_quotient(n, d) * d) by {
            rewrite(0, 0 * d);
            close();
        }
        have 0 + truncating_remainder(n, d) <= (truncating_quotient(n, d) * d) + truncating_remainder(n, d) by {
            apply(integer::add_le(0, (truncating_quotient(n, d) * d), truncating_remainder(n, d), truncating_remainder(n, d)));
        }
        have truncating_remainder(n, d) == 0 + truncating_remainder(n, d) by {
            close();
        }
        have n == (truncating_quotient(n, d) * d) + truncating_remainder(n, d) by {
            close();
        }
        apply(integer::le_substitute(0 + truncating_remainder(n, d), (truncating_quotient(n, d) * d) + truncating_remainder(n, d), truncating_remainder(n, d), n));
    }
}

theorem nonpositive_dividend_remainder_lower(n: Integer, d: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires n <= 0;
    ensures n <= truncating_remainder(n, d) by {
        have 0 < d by {
            have 0 + 1 <= d by {
                close();
            }
            apply(integer::step_le_lt(0, d));
        }
        have 0 <= d by {
            apply(integer::lt_le(0, d));
        }
        have n == (truncating_quotient(n, d) * d) + truncating_remainder(n, d) by {
            apply(integer::truncation_identity(n, d));
        }
        have n + -(truncating_remainder(n, d)) == (truncating_quotient(n, d) * d) by {
            apply(integer::sum_difference(n, (truncating_quotient(n, d) * d), truncating_remainder(n, d)));
        }
        have -(truncating_quotient(n, d) * d) == -n + truncating_remainder(n, d) by {
            apply(integer::sum_difference(n, (truncating_quotient(n, d) * d), truncating_remainder(n, d)));
        }
        have n == truncating_remainder(n, d) + (truncating_quotient(n, d) * d) by {
            apply(integer::sum_commute(n, (truncating_quotient(n, d) * d), truncating_remainder(n, d)));
        }
        have 0 * d == 0 by {
            close();
        }
        have n <= 0 * d by {
            rewrite(0 * d, 0);
            close();
        }
        have truncating_quotient(n, d) <= 0 by {
            apply(integer::positive_divisor_quotient_upper(n, d, 0));
        }
        have (truncating_quotient(n, d) * d) <= 0 * d by {
            apply(integer::multiply_order_nonnegative(truncating_quotient(n, d), 0, d));
        }
        have (truncating_quotient(n, d) * d) <= 0 by {
            rewrite(0, 0 * d);
            close();
        }
        have (truncating_quotient(n, d) * d) + truncating_remainder(n, d) <= 0 + truncating_remainder(n, d) by {
            apply(integer::add_le((truncating_quotient(n, d) * d), 0, truncating_remainder(n, d), truncating_remainder(n, d)));
        }
        have n == (truncating_quotient(n, d) * d) + truncating_remainder(n, d) by {
            close();
        }
        have truncating_remainder(n, d) == 0 + truncating_remainder(n, d) by {
            close();
        }
        apply(integer::le_substitute((truncating_quotient(n, d) * d) + truncating_remainder(n, d), 0 + truncating_remainder(n, d), n, truncating_remainder(n, d)));
    }
}

theorem quotient_upper_interval_nonnegative(n: Integer, d: Integer, numerator_bound: Integer, endpoint: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires 0 <= bound;
    requires endpoint <= d;
    requires n <= numerator_bound;
    requires numerator_bound <= bound * endpoint + (endpoint - 1);
    ensures truncating_quotient(n, d) <= bound by {
        have bound * endpoint <= bound * d by {
            have endpoint * bound <= d * bound by {
                apply(integer::multiply_order_nonnegative(endpoint, d, bound));
            }
            have bound * endpoint == endpoint * bound by {
                apply(integer::multiply_commutative(bound, endpoint));
            }
            have bound * d == d * bound by {
                apply(integer::multiply_commutative(bound, d));
            }
            have bound * endpoint == endpoint * bound by {
                rewrite(bound * endpoint, endpoint * bound);
                close();
            }
            have bound * d == d * bound by {
                rewrite(bound * d, d * bound);
                close();
            }
            apply(integer::le_substitute(endpoint * bound, d * bound, bound * endpoint, bound * d));
        }
        have endpoint - 1 <= d - 1 by {
            apply(integer::subtract_right_order(endpoint, d, 1));
        }
        have bound * endpoint + (endpoint - 1) <= bound * d + (d - 1) by {
            apply(integer::add_le(bound * endpoint, bound * d, endpoint - 1, d - 1));
        }
        have numerator_bound <= bound * d + (d - 1) by {
            apply(integer::le_transitive(numerator_bound, bound * endpoint + (endpoint - 1), bound * d + (d - 1)));
        }
        have n <= bound * d + (d - 1) by {
            apply(integer::le_transitive(n, numerator_bound, bound * d + (d - 1)));
        }
        if n <= 0 {
            have 0 * d == 0 by {
                close();
            }
            have n <= 0 * d by {
                rewrite(0 * d, 0);
                close();
            }
            have truncating_quotient(n, d) <= 0 by {
                apply(integer::positive_divisor_quotient_upper(n, d, 0));
            }
            apply(integer::le_transitive(truncating_quotient(n, d), 0, bound));
        } else {
            have 0 < n by {
                close();
            }
            have 0 <= n by {
                apply(integer::lt_le(0, n));
            }
            apply(integer::positive_divisor_quotient_upper_rounded(n, d, bound));
        }
    }
}

theorem quotient_lower_interval_nonpositive(n: Integer, d: Integer, numerator_bound: Integer, endpoint: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires bound <= 0;
    requires endpoint <= d;
    requires numerator_bound <= n;
    requires bound * endpoint - (endpoint - 1) <= numerator_bound;
    ensures bound <= truncating_quotient(n, d) by {
        have bound * d <= bound * endpoint by {
            have d * bound <= endpoint * bound by {
                apply(integer::multiply_order_nonpositive(endpoint, d, bound));
            }
            have bound * d == d * bound by {
                apply(integer::multiply_commutative(bound, d));
            }
            have bound * endpoint == endpoint * bound by {
                apply(integer::multiply_commutative(bound, endpoint));
            }
            have bound * d == d * bound by {
                rewrite(bound * d, d * bound);
                close();
            }
            have bound * endpoint == endpoint * bound by {
                rewrite(bound * endpoint, endpoint * bound);
                close();
            }
            apply(integer::le_substitute(d * bound, endpoint * bound, bound * d, bound * endpoint));
        }
        have endpoint - 1 <= d - 1 by {
            apply(integer::subtract_right_order(endpoint, d, 1));
        }
        have -(d - 1) <= -(endpoint - 1) by {
            apply(integer::negate_order(endpoint - 1, d - 1));
        }
        have bound * d + -(d - 1) <= bound * endpoint + -(endpoint - 1) by {
            apply(integer::add_le(bound * d, bound * endpoint, -(d - 1), -(endpoint - 1)));
        }
        have bound * d - (d - 1) <= bound * endpoint - (endpoint - 1) by {
            have bound * d - (d - 1) == bound * d + -(d - 1) by {
                close();
            }
            have bound * endpoint - (endpoint - 1) == bound * endpoint + -(endpoint - 1) by {
                close();
            }
            apply(integer::le_substitute(bound * d + -(d - 1), bound * endpoint + -(endpoint - 1), bound * d - (d - 1), bound * endpoint - (endpoint - 1)));
        }
        have bound * d - (d - 1) <= numerator_bound by {
            apply(integer::le_transitive(bound * d - (d - 1), bound * endpoint - (endpoint - 1), numerator_bound));
        }
        have bound * d - (d - 1) <= n by {
            apply(integer::le_transitive(bound * d - (d - 1), numerator_bound, n));
        }
        if 0 <= n {
            have 0 * d == 0 by {
                close();
            }
            have 0 * d <= n by {
                rewrite(0 * d, 0);
                close();
            }
            have 0 <= truncating_quotient(n, d) by {
                apply(integer::positive_divisor_quotient_lower(n, d, 0));
            }
            apply(integer::le_transitive(bound, 0, truncating_quotient(n, d)));
        } else {
            have n < 0 by {
                close();
            }
            have n <= 0 by {
                apply(integer::lt_le(n, 0));
            }
            apply(integer::positive_divisor_quotient_lower_rounded(n, d, bound));
        }
    }
}

theorem quotient_upper_interval_negative(n: Integer, d: Integer, numerator_bound: Integer, endpoint: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires bound <= 0;
    requires d <= endpoint;
    requires n <= numerator_bound;
    requires numerator_bound <= bound * endpoint;
    ensures truncating_quotient(n, d) <= bound by {
        have bound * endpoint <= bound * d by {
            have endpoint * bound <= d * bound by {
                apply(integer::multiply_order_nonpositive(d, endpoint, bound));
            }
            have bound * endpoint == endpoint * bound by {
                apply(integer::multiply_commutative(bound, endpoint));
            }
            have bound * d == d * bound by {
                apply(integer::multiply_commutative(bound, d));
            }
            have bound * endpoint == endpoint * bound by {
                rewrite(bound * endpoint, endpoint * bound);
                close();
            }
            have bound * d == d * bound by {
                rewrite(bound * d, d * bound);
                close();
            }
            apply(integer::le_substitute(endpoint * bound, d * bound, bound * endpoint, bound * d));
        }
        have n <= bound * endpoint by {
            apply(integer::le_transitive(n, numerator_bound, bound * endpoint));
        }
        have n <= bound * d by {
            apply(integer::le_transitive(n, bound * endpoint, bound * d));
        }
        apply(integer::positive_divisor_quotient_upper(n, d, bound));
    }
}

theorem quotient_lower_interval_positive(n: Integer, d: Integer, numerator_bound: Integer, endpoint: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires 0 <= bound;
    requires d <= endpoint;
    requires numerator_bound <= n;
    requires bound * endpoint <= numerator_bound;
    ensures bound <= truncating_quotient(n, d) by {
        have bound * d <= bound * endpoint by {
            have d * bound <= endpoint * bound by {
                apply(integer::multiply_order_nonnegative(d, endpoint, bound));
            }
            have bound * d == d * bound by {
                apply(integer::multiply_commutative(bound, d));
            }
            have bound * endpoint == endpoint * bound by {
                apply(integer::multiply_commutative(bound, endpoint));
            }
            have bound * d == d * bound by {
                rewrite(bound * d, d * bound);
                close();
            }
            have bound * endpoint == endpoint * bound by {
                rewrite(bound * endpoint, endpoint * bound);
                close();
            }
            apply(integer::le_substitute(d * bound, endpoint * bound, bound * d, bound * endpoint));
        }
        have bound * d <= numerator_bound by {
            apply(integer::le_transitive(bound * d, bound * endpoint, numerator_bound));
        }
        have bound * d <= n by {
            apply(integer::le_transitive(bound * d, numerator_bound, n));
        }
        apply(integer::positive_divisor_quotient_lower(n, d, bound));
    }
}

theorem remainder_lower_from_dividend(n: Integer, d: Integer, numerator_bound: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires numerator_bound <= n;
    requires bound <= numerator_bound;
    requires bound <= 0;
    ensures bound <= truncating_remainder(n, d) by {
        if n <= 0 {
            have n <= truncating_remainder(n, d) by {
                apply(integer::nonpositive_dividend_remainder_lower(n, d));
            }
            have bound <= n by {
                apply(integer::le_transitive(bound, numerator_bound, n));
            }
            apply(integer::le_transitive(bound, n, truncating_remainder(n, d)));
        } else {
            have 0 < n by {
                close();
            }
            have 0 <= n by {
                apply(integer::lt_le(0, n));
            }
            have 0 <= truncating_remainder(n, d) by {
                apply(integer::nonnegative_dividend_remainder(n, d));
            }
            apply(integer::le_transitive(bound, 0, truncating_remainder(n, d)));
        }
    }
}

theorem remainder_lower_from_divisor(n: Integer, d: Integer, endpoint: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires d <= endpoint;
    requires bound <= 1 - endpoint;
    ensures bound <= truncating_remainder(n, d) by {
        have 0 < d by {
            have 0 + 1 <= d by {
                close();
            }
            apply(integer::step_le_lt(0, d));
        }
        have 1 - d <= truncating_remainder(n, d) by {
            apply(integer::positive_divisor_remainder_lower(n, d));
        }
        have 1 - endpoint <= 1 - d by {
            apply(integer::subtract_left_order(d, endpoint, 1));
        }
        have bound <= 1 - d by {
            apply(integer::le_transitive(bound, 1 - endpoint, 1 - d));
        }
        apply(integer::le_transitive(bound, 1 - d, truncating_remainder(n, d)));
    }
}

theorem remainder_upper_from_dividend(n: Integer, d: Integer, numerator_bound: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires n <= numerator_bound;
    requires numerator_bound <= bound;
    requires 0 <= bound;
    ensures truncating_remainder(n, d) <= bound by {
        if 0 <= n {
            have truncating_remainder(n, d) <= n by {
                apply(integer::nonnegative_dividend_remainder_upper(n, d));
            }
            have n <= bound by {
                apply(integer::le_transitive(n, numerator_bound, bound));
            }
            apply(integer::le_transitive(truncating_remainder(n, d), n, bound));
        } else {
            have n < 0 by {
                close();
            }
            have n <= 0 by {
                apply(integer::lt_le(n, 0));
            }
            have truncating_remainder(n, d) <= 0 by {
                apply(integer::nonpositive_dividend_remainder(n, d));
            }
            apply(integer::le_transitive(truncating_remainder(n, d), 0, bound));
        }
    }
}

theorem remainder_upper_from_divisor(n: Integer, d: Integer, endpoint: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires d <= endpoint;
    requires endpoint - 1 <= bound;
    ensures truncating_remainder(n, d) <= bound by {
        have 0 < d by {
            have 0 + 1 <= d by {
                close();
            }
            apply(integer::step_le_lt(0, d));
        }
        have truncating_remainder(n, d) <= d - 1 by {
            apply(integer::positive_divisor_remainder_upper(n, d));
        }
        have d - 1 <= endpoint - 1 by {
            apply(integer::subtract_right_order(d, endpoint, 1));
        }
        have truncating_remainder(n, d) <= endpoint - 1 by {
            apply(integer::le_transitive(truncating_remainder(n, d), d - 1, endpoint - 1));
        }
        apply(integer::le_transitive(truncating_remainder(n, d), endpoint - 1, bound));
    }
}

theorem small_remainder_interval(n: Integer, d: Integer, lo_n: Integer, hi_n: Integer, endpoint: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires endpoint <= d;
    requires lo_n <= n;
    requires n <= hi_n;
    requires 1 - endpoint <= lo_n;
    requires hi_n <= endpoint - 1;
    ensures truncating_remainder(n, d) == n by {
        have 0 * endpoint - (endpoint - 1) <= lo_n by {
            have 0 * endpoint - (endpoint - 1) == 1 - endpoint by {
                close();
            }
            rewrite(0 * endpoint - (endpoint - 1), 1 - endpoint);
            close();
        }
        have hi_n <= 0 * endpoint + (endpoint - 1) by {
            have 0 * endpoint + (endpoint - 1) == endpoint - 1 by {
                close();
            }
            rewrite(0 * endpoint + (endpoint - 1), endpoint - 1);
            close();
        }
        have 0 <= truncating_quotient(n, d) by {
            apply(integer::quotient_lower_interval_nonpositive(n, d, lo_n, endpoint, 0));
        }
        have truncating_quotient(n, d) <= 0 by {
            apply(integer::quotient_upper_interval_nonnegative(n, d, hi_n, endpoint, 0));
        }
        have truncating_quotient(n, d) == 0 by {
            apply(integer::le_antisymmetric(truncating_quotient(n, d), 0));
        }
        have n == (truncating_quotient(n, d) * d) + truncating_remainder(n, d) by {
            apply(integer::truncation_identity(n, d));
        }
        have truncating_remainder(n, d) == (truncating_quotient(n, d) * d) + truncating_remainder(n, d) by {
            rewrite(truncating_quotient(n, d), 0);
            close();
        }
        have (truncating_quotient(n, d) * d) + truncating_remainder(n, d) == n by {
            close();
        }
        apply(integer::equal_substitute((truncating_quotient(n, d) * d) + truncating_remainder(n, d), n, truncating_remainder(n, d), n));
    }
}

theorem nonzero_from_one(d: Integer) {
    requires 1 <= d;
    let one: Integer = 1;
    ensures d != 0 by {
        if d == 0 {
            have one <= 0 by {
                apply(integer::le_substitute(one, d, one, 0));
            }
            contradiction(one <= 0);
        } else { close(); }
    }
}
theorem nonzero_from_negative_one(d: Integer) {
    requires d <= -1;
    let zero: Integer = 0;
    ensures d != 0 by {
        if d == 0 {
            have zero <= -1 by {
                apply(integer::le_substitute(d, -1, zero, -1));
            }
            contradiction(zero <= -1);
        } else { close(); }
    }
}

theorem quotient_negate_divisor(n: Integer, d: Integer) {
    requires d != 0;
    requires -d != 0;
    ensures truncating_quotient(n, d) == -truncating_quotient(n, -d);
}

theorem remainder_negate_divisor(n: Integer, d: Integer) {
    requires d != 0;
    requires -d != 0;
    ensures truncating_remainder(n, d) == truncating_remainder(n, -d);
}

// Reconstruct a nonnegative truncating quotient from its explicit remainder.
theorem nonnegative_quotient_from_remainder(n: Integer, d: Integer, q: Integer, r: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires 0 <= n;
    requires 0 <= r;
    requires r <= d - 1;
    requires n == q * d + r;
    ensures truncating_quotient(n, d) == q by {
        have q * d + 0 <= q * d + r by {
            apply(integer::add_le(q * d, q * d, 0, r));
        }
        have q * d == q * d + 0 by close();
        have q * d <= n by {
            apply(integer::le_substitute(q * d + 0, q * d + r, q * d, n));
        }
        have q <= truncating_quotient(n, d) by {
            apply(integer::positive_divisor_quotient_lower(n, d, q));
        }
        have q * d + r <= q * d + (d - 1) by {
            apply(integer::add_le(q * d, q * d, r, d - 1));
        }
        have n <= q * d + (d - 1) by {
            apply(integer::le_substitute(q * d + r, q * d + (d - 1), n, q * d + (d - 1)));
        }
        have truncating_quotient(n, d) <= q by {
            apply(integer::positive_divisor_quotient_upper_rounded(n, d, q));
        }
        apply(integer::le_antisymmetric(truncating_quotient(n, d), q));
    }
}

theorem uint32_less_than_divisor_implies_remainder_is_value(value: uint32, divisor: uint32) {
    requires value < divisor;
    ensures value % divisor == value by {
        if divisor != 0u32 {
            have 0 <= to_integer(value) by close();
            have to_integer(value) + 1 <= to_integer(divisor) by {
                apply(integer::lt_step_le(to_integer(value), to_integer(divisor)));
            }
            have 0 + 1 <= to_integer(divisor) by {
                have 0 + 1 <= to_integer(value) + 1 by {
                    apply(integer::add_right_order(0, to_integer(value), 1));
                }
                apply(integer::le_transitive(0 + 1, to_integer(value) + 1, to_integer(divisor)));
            }
            have 1 <= to_integer(divisor) by close();
            have 0 < to_integer(divisor) by {
                apply(integer::step_le_lt(0, to_integer(divisor)));
            }
            have to_integer(divisor) != 0 by close();
            have to_integer(value) <= to_integer(divisor) - 1 by {
                apply(integer::lt_le_predecessor(to_integer(value), to_integer(divisor)));
            }
            have to_integer(value) == 0 * to_integer(divisor) + to_integer(value) by close();
            apply(integer::nonnegative_quotient_from_remainder(to_integer(value), to_integer(divisor), 0, to_integer(value)));
            apply(integer::truncation_identity(to_integer(value), to_integer(divisor)));
            apply(integer::uint32_remainder_to_integer(value, divisor));
            have to_integer(value) == truncating_remainder(to_integer(value), to_integer(divisor)) by {
                have truncating_remainder(to_integer(value), to_integer(divisor)) == 0 * to_integer(divisor) + truncating_remainder(to_integer(value), to_integer(divisor)) by close();
                rewrite(truncating_remainder(to_integer(value), to_integer(divisor)), 0 * to_integer(divisor) + truncating_remainder(to_integer(value), to_integer(divisor)));
                rewrite(0, truncating_quotient(to_integer(value), to_integer(divisor)));
                close();
            }
            have to_integer(value % divisor) == to_integer(value) by {
                rewrite(to_integer(value % divisor), truncating_remainder(to_integer(value), to_integer(divisor)));
                close();
            }
            close();
        } else {
            have divisor == 0u32 by close();
            have to_integer(divisor) == 0 by close();
            have to_integer(value) < 0 by {
                rewrite(0, to_integer(divisor));
                close();
            }
            have 0 <= to_integer(value) by close();
            contradiction(to_integer(value) < 0);
        }
    }
}

theorem nonnegative_quotient_shift(x: Integer, d: Integer, k: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires 0 <= x;
    requires 0 <= k;
    ensures truncating_quotient(x + d * k, d) == truncating_quotient(x, d) + k by {
        have 0 <= d by { apply(integer::le_transitive(0, 1, d)); }
        have 0 * d <= k * d by {
            apply(integer::multiply_order_nonnegative(0, k, d));
        }
        have 0 * d == 0 by close();
        have d * k == k * d by { apply(integer::multiply_commutative(d, k)); }
        have 0 <= d * k by {
            apply(integer::le_substitute(0 * d, k * d, 0, d * k));
        }
        have 0 + 0 <= x + d * k by {
            apply(integer::add_le(0, x, 0, d * k));
        }
        have 0 + 0 == 0 by close();
        have 0 <= x + d * k by close();
        have x == truncating_quotient(x, d) * d + truncating_remainder(x, d) by {
            apply(integer::truncation_identity(x, d));
        }
        have 0 <= truncating_remainder(x, d) by {
            apply(integer::nonnegative_dividend_remainder(x, d));
        }
        have 0 < d by { apply(integer::step_le_lt(0, d)); }
        have truncating_remainder(x, d) <= d - 1 by {
            apply(integer::positive_divisor_remainder_upper(x, d));
        }
        have x + d * k == (truncating_quotient(x, d) * d + truncating_remainder(x, d)) + d * k by {
            apply(integer::equal_add(x, truncating_quotient(x, d) * d + truncating_remainder(x, d), d * k, d * k));
        }
        have (truncating_quotient(x, d) + k) * d == truncating_quotient(x, d) * d + k * d by {
            apply(integer::multiply_add(truncating_quotient(x, d), k, d));
        }
        have (truncating_quotient(x, d) * d + truncating_remainder(x, d)) + d * k == (truncating_quotient(x, d) + k) * d + truncating_remainder(x, d) by {
            rewrite((truncating_quotient(x, d) + k) * d, truncating_quotient(x, d) * d + k * d);
            rewrite(d * k, k * d);
            close();
        }
        have x + d * k == (truncating_quotient(x, d) + k) * d + truncating_remainder(x, d) by close();
        apply(integer::nonnegative_quotient_from_remainder(x + d * k, d, truncating_quotient(x, d) + k, truncating_remainder(x, d)));
    }
}

// Recover the remainder from an explicitly bounded Euclidean reconstruction.
theorem nonnegative_remainder_from_reconstruction(n: Integer, d: Integer, q: Integer, r: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires 0 <= n;
    requires 0 <= r;
    requires r <= d - 1;
    requires n == q * d + r;
    ensures truncating_remainder(n, d) == r by {
        apply(integer::nonnegative_quotient_from_remainder(n, d, q, r));
        apply(integer::truncation_identity(n, d));
        have n == q * d + truncating_remainder(n, d) by close();
        have n == truncating_remainder(n, d) + q * d by {
            apply(integer::sum_commute(n, q * d, truncating_remainder(n, d)));
        }
        have n == r + q * d by {
            apply(integer::sum_commute(n, q * d, r));
        }
        apply(integer::sum_difference(n, truncating_remainder(n, d), q * d));
        apply(integer::sum_difference(n, r, q * d));
        close();
    }
}

// Same-element pointer translation from a pointer relation and exact Integer
// displacement equality. Address-word equality grants no pointer relation.
axiom uint8_pointer_translate_int32(p: uint8*, q: uint8*, a: int32, b: int32, c: int32, d: int32) {
    requires p + a == q + b;
    requires to_integer(c) - to_integer(a) == to_integer(d) - to_integer(b);
    ensures p + c == q + d;
}

theorem uint8_pointer_add_associate_int32(p: uint8*, i: int32, j: int32) {
    requires defined(i + j);
    ensures (p + i) + j == p + (i + j) by {
        apply(integer::int32_add_to_integer(i, j));
        have (p + i) + 0 == p + i by close();
        have to_integer(j) - 0 == to_integer(i + j) - to_integer(i) by {
            rewrite(to_integer(i + j), to_integer(i) + to_integer(j));
            close();
        }
        apply(integer::uint8_pointer_translate_int32(p + i, p, 0, i, j, i + j));
    }
}

axiom uint8_pointer_translate_uint64(p: uint8*, q: uint8*, a: uint64, b: uint64, c: uint64, d: uint64) {
    requires p + a == q + b;
    requires to_integer(c) - to_integer(a) == to_integer(d) - to_integer(b);
    ensures p + c == q + d;
}

theorem uint8_pointer_add_associate_uint64(p: uint8*, i: uint64, j: uint64) {
    requires to_integer(i) + to_integer(j) <= 18446744073709551615;
    ensures (p + i) + j == p + (i + j) by {
        apply(integer::uint64_add_to_integer(i, j));
        have (p + i) + 0u64 == p + i by close();
        have to_integer(j) - 0 == to_integer(i + j) - to_integer(i) by {
            rewrite(to_integer(i + j), to_integer(i) + to_integer(j));
            close();
        }
        apply(integer::uint8_pointer_translate_uint64(p + i, p, 0u64, i, j, i + j));
    }
}

axiom int8_pointer_translate_int32(p: int8*, q: int8*, a: int32, b: int32, c: int32, d: int32) {
    requires p + a == q + b;
    requires to_integer(c) - to_integer(a) == to_integer(d) - to_integer(b);
    ensures p + c == q + d;
}

theorem int8_pointer_add_associate_int32(p: int8*, i: int32, j: int32) {
    requires defined(i + j);
    ensures (p + i) + j == p + (i + j) by {
        apply(integer::int32_add_to_integer(i, j));
        have (p + i) + 0 == p + i by close();
        have to_integer(j) - 0 == to_integer(i + j) - to_integer(i) by {
            rewrite(to_integer(i + j), to_integer(i) + to_integer(j));
            close();
        }
        apply(integer::int8_pointer_translate_int32(p + i, p, 0, i, j, i + j));
    }
}

axiom int8_pointer_translate_uint64(p: int8*, q: int8*, a: uint64, b: uint64, c: uint64, d: uint64) {
    requires p + a == q + b;
    requires to_integer(c) - to_integer(a) == to_integer(d) - to_integer(b);
    ensures p + c == q + d;
}

theorem int8_pointer_add_associate_uint64(p: int8*, i: uint64, j: uint64) {
    requires to_integer(i) + to_integer(j) <= 18446744073709551615;
    ensures (p + i) + j == p + (i + j) by {
        apply(integer::uint64_add_to_integer(i, j));
        have (p + i) + 0u64 == p + i by close();
        have to_integer(j) - 0 == to_integer(i + j) - to_integer(i) by {
            rewrite(to_integer(i + j), to_integer(i) + to_integer(j));
            close();
        }
        apply(integer::int8_pointer_translate_uint64(p + i, p, 0u64, i, j, i + j));
    }
}

axiom uint16_pointer_translate_int32(p: uint16*, q: uint16*, a: int32, b: int32, c: int32, d: int32) {
    requires p + a == q + b;
    requires to_integer(c) - to_integer(a) == to_integer(d) - to_integer(b);
    ensures p + c == q + d;
}

theorem uint16_pointer_add_associate_int32(p: uint16*, i: int32, j: int32) {
    requires defined(i + j);
    ensures (p + i) + j == p + (i + j) by {
        apply(integer::int32_add_to_integer(i, j));
        have (p + i) + 0 == p + i by close();
        have to_integer(j) - 0 == to_integer(i + j) - to_integer(i) by {
            rewrite(to_integer(i + j), to_integer(i) + to_integer(j));
            close();
        }
        apply(integer::uint16_pointer_translate_int32(p + i, p, 0, i, j, i + j));
    }
}

axiom uint16_pointer_translate_uint64(p: uint16*, q: uint16*, a: uint64, b: uint64, c: uint64, d: uint64) {
    requires p + a == q + b;
    requires to_integer(c) - to_integer(a) == to_integer(d) - to_integer(b);
    ensures p + c == q + d;
}

theorem uint16_pointer_add_associate_uint64(p: uint16*, i: uint64, j: uint64) {
    requires to_integer(i) + to_integer(j) <= 18446744073709551615;
    ensures (p + i) + j == p + (i + j) by {
        apply(integer::uint64_add_to_integer(i, j));
        have (p + i) + 0u64 == p + i by close();
        have to_integer(j) - 0 == to_integer(i + j) - to_integer(i) by {
            rewrite(to_integer(i + j), to_integer(i) + to_integer(j));
            close();
        }
        apply(integer::uint16_pointer_translate_uint64(p + i, p, 0u64, i, j, i + j));
    }
}

axiom int16_pointer_translate_int32(p: int16*, q: int16*, a: int32, b: int32, c: int32, d: int32) {
    requires p + a == q + b;
    requires to_integer(c) - to_integer(a) == to_integer(d) - to_integer(b);
    ensures p + c == q + d;
}

theorem int16_pointer_add_associate_int32(p: int16*, i: int32, j: int32) {
    requires defined(i + j);
    ensures (p + i) + j == p + (i + j) by {
        apply(integer::int32_add_to_integer(i, j));
        have (p + i) + 0 == p + i by close();
        have to_integer(j) - 0 == to_integer(i + j) - to_integer(i) by {
            rewrite(to_integer(i + j), to_integer(i) + to_integer(j));
            close();
        }
        apply(integer::int16_pointer_translate_int32(p + i, p, 0, i, j, i + j));
    }
}

axiom int16_pointer_translate_uint64(p: int16*, q: int16*, a: uint64, b: uint64, c: uint64, d: uint64) {
    requires p + a == q + b;
    requires to_integer(c) - to_integer(a) == to_integer(d) - to_integer(b);
    ensures p + c == q + d;
}

theorem int16_pointer_add_associate_uint64(p: int16*, i: uint64, j: uint64) {
    requires to_integer(i) + to_integer(j) <= 18446744073709551615;
    ensures (p + i) + j == p + (i + j) by {
        apply(integer::uint64_add_to_integer(i, j));
        have (p + i) + 0u64 == p + i by close();
        have to_integer(j) - 0 == to_integer(i + j) - to_integer(i) by {
            rewrite(to_integer(i + j), to_integer(i) + to_integer(j));
            close();
        }
        apply(integer::int16_pointer_translate_uint64(p + i, p, 0u64, i, j, i + j));
    }
}

axiom uint32_pointer_translate_int32(p: uint32*, q: uint32*, a: int32, b: int32, c: int32, d: int32) {
    requires p + a == q + b;
    requires to_integer(c) - to_integer(a) == to_integer(d) - to_integer(b);
    ensures p + c == q + d;
}

theorem uint32_pointer_add_associate_int32(p: uint32*, i: int32, j: int32) {
    requires defined(i + j);
    ensures (p + i) + j == p + (i + j) by {
        apply(integer::int32_add_to_integer(i, j));
        have (p + i) + 0 == p + i by close();
        have to_integer(j) - 0 == to_integer(i + j) - to_integer(i) by {
            rewrite(to_integer(i + j), to_integer(i) + to_integer(j));
            close();
        }
        apply(integer::uint32_pointer_translate_int32(p + i, p, 0, i, j, i + j));
    }
}

axiom uint32_pointer_translate_uint64(p: uint32*, q: uint32*, a: uint64, b: uint64, c: uint64, d: uint64) {
    requires p + a == q + b;
    requires to_integer(c) - to_integer(a) == to_integer(d) - to_integer(b);
    ensures p + c == q + d;
}

theorem uint32_pointer_add_associate_uint64(p: uint32*, i: uint64, j: uint64) {
    requires to_integer(i) + to_integer(j) <= 18446744073709551615;
    ensures (p + i) + j == p + (i + j) by {
        apply(integer::uint64_add_to_integer(i, j));
        have (p + i) + 0u64 == p + i by close();
        have to_integer(j) - 0 == to_integer(i + j) - to_integer(i) by {
            rewrite(to_integer(i + j), to_integer(i) + to_integer(j));
            close();
        }
        apply(integer::uint32_pointer_translate_uint64(p + i, p, 0u64, i, j, i + j));
    }
}

axiom int32_pointer_translate_int32(p: int32*, q: int32*, a: int32, b: int32, c: int32, d: int32) {
    requires p + a == q + b;
    requires to_integer(c) - to_integer(a) == to_integer(d) - to_integer(b);
    ensures p + c == q + d;
}

theorem int32_pointer_add_associate_int32(p: int32*, i: int32, j: int32) {
    requires defined(i + j);
    ensures (p + i) + j == p + (i + j) by {
        apply(integer::int32_add_to_integer(i, j));
        have (p + i) + 0 == p + i by close();
        have to_integer(j) - 0 == to_integer(i + j) - to_integer(i) by {
            rewrite(to_integer(i + j), to_integer(i) + to_integer(j));
            close();
        }
        apply(integer::int32_pointer_translate_int32(p + i, p, 0, i, j, i + j));
    }
}

axiom int32_pointer_translate_uint64(p: int32*, q: int32*, a: uint64, b: uint64, c: uint64, d: uint64) {
    requires p + a == q + b;
    requires to_integer(c) - to_integer(a) == to_integer(d) - to_integer(b);
    ensures p + c == q + d;
}

theorem int32_pointer_add_associate_uint64(p: int32*, i: uint64, j: uint64) {
    requires to_integer(i) + to_integer(j) <= 18446744073709551615;
    ensures (p + i) + j == p + (i + j) by {
        apply(integer::uint64_add_to_integer(i, j));
        have (p + i) + 0u64 == p + i by close();
        have to_integer(j) - 0 == to_integer(i + j) - to_integer(i) by {
            rewrite(to_integer(i + j), to_integer(i) + to_integer(j));
            close();
        }
        apply(integer::int32_pointer_translate_uint64(p + i, p, 0u64, i, j, i + j));
    }
}

axiom uint64_pointer_translate_int32(p: uint64*, q: uint64*, a: int32, b: int32, c: int32, d: int32) {
    requires p + a == q + b;
    requires to_integer(c) - to_integer(a) == to_integer(d) - to_integer(b);
    ensures p + c == q + d;
}

theorem uint64_pointer_add_associate_int32(p: uint64*, i: int32, j: int32) {
    requires defined(i + j);
    ensures (p + i) + j == p + (i + j) by {
        apply(integer::int32_add_to_integer(i, j));
        have (p + i) + 0 == p + i by close();
        have to_integer(j) - 0 == to_integer(i + j) - to_integer(i) by {
            rewrite(to_integer(i + j), to_integer(i) + to_integer(j));
            close();
        }
        apply(integer::uint64_pointer_translate_int32(p + i, p, 0, i, j, i + j));
    }
}

axiom uint64_pointer_translate_uint64(p: uint64*, q: uint64*, a: uint64, b: uint64, c: uint64, d: uint64) {
    requires p + a == q + b;
    requires to_integer(c) - to_integer(a) == to_integer(d) - to_integer(b);
    ensures p + c == q + d;
}

theorem uint64_pointer_add_associate_uint64(p: uint64*, i: uint64, j: uint64) {
    requires to_integer(i) + to_integer(j) <= 18446744073709551615;
    ensures (p + i) + j == p + (i + j) by {
        apply(integer::uint64_add_to_integer(i, j));
        have (p + i) + 0u64 == p + i by close();
        have to_integer(j) - 0 == to_integer(i + j) - to_integer(i) by {
            rewrite(to_integer(i + j), to_integer(i) + to_integer(j));
            close();
        }
        apply(integer::uint64_pointer_translate_uint64(p + i, p, 0u64, i, j, i + j));
    }
}

axiom int64_pointer_translate_int32(p: int64*, q: int64*, a: int32, b: int32, c: int32, d: int32) {
    requires p + a == q + b;
    requires to_integer(c) - to_integer(a) == to_integer(d) - to_integer(b);
    ensures p + c == q + d;
}

theorem int64_pointer_add_associate_int32(p: int64*, i: int32, j: int32) {
    requires defined(i + j);
    ensures (p + i) + j == p + (i + j) by {
        apply(integer::int32_add_to_integer(i, j));
        have (p + i) + 0 == p + i by close();
        have to_integer(j) - 0 == to_integer(i + j) - to_integer(i) by {
            rewrite(to_integer(i + j), to_integer(i) + to_integer(j));
            close();
        }
        apply(integer::int64_pointer_translate_int32(p + i, p, 0, i, j, i + j));
    }
}

axiom int64_pointer_translate_uint64(p: int64*, q: int64*, a: uint64, b: uint64, c: uint64, d: uint64) {
    requires p + a == q + b;
    requires to_integer(c) - to_integer(a) == to_integer(d) - to_integer(b);
    ensures p + c == q + d;
}

theorem int64_pointer_add_associate_uint64(p: int64*, i: uint64, j: uint64) {
    requires to_integer(i) + to_integer(j) <= 18446744073709551615;
    ensures (p + i) + j == p + (i + j) by {
        apply(integer::uint64_add_to_integer(i, j));
        have (p + i) + 0u64 == p + i by close();
        have to_integer(j) - 0 == to_integer(i + j) - to_integer(i) by {
            rewrite(to_integer(i + j), to_integer(i) + to_integer(j));
            close();
        }
        apply(integer::int64_pointer_translate_uint64(p + i, p, 0u64, i, j, i + j));
    }
}

axiom float32_pointer_translate_int32(p: float*, q: float*, a: int32, b: int32, c: int32, d: int32) {
    requires p + a == q + b;
    requires to_integer(c) - to_integer(a) == to_integer(d) - to_integer(b);
    ensures p + c == q + d;
}

theorem float32_pointer_add_associate_int32(p: float*, i: int32, j: int32) {
    requires defined(i + j);
    ensures (p + i) + j == p + (i + j) by {
        apply(integer::int32_add_to_integer(i, j));
        have (p + i) + 0 == p + i by close();
        have to_integer(j) - 0 == to_integer(i + j) - to_integer(i) by {
            rewrite(to_integer(i + j), to_integer(i) + to_integer(j));
            close();
        }
        apply(integer::float32_pointer_translate_int32(p + i, p, 0, i, j, i + j));
    }
}

axiom float32_pointer_translate_uint64(p: float*, q: float*, a: uint64, b: uint64, c: uint64, d: uint64) {
    requires p + a == q + b;
    requires to_integer(c) - to_integer(a) == to_integer(d) - to_integer(b);
    ensures p + c == q + d;
}

theorem float32_pointer_add_associate_uint64(p: float*, i: uint64, j: uint64) {
    requires to_integer(i) + to_integer(j) <= 18446744073709551615;
    ensures (p + i) + j == p + (i + j) by {
        apply(integer::uint64_add_to_integer(i, j));
        have (p + i) + 0u64 == p + i by close();
        have to_integer(j) - 0 == to_integer(i + j) - to_integer(i) by {
            rewrite(to_integer(i + j), to_integer(i) + to_integer(j));
            close();
        }
        apply(integer::float32_pointer_translate_uint64(p + i, p, 0u64, i, j, i + j));
    }
}

axiom float64_pointer_translate_int32(p: double*, q: double*, a: int32, b: int32, c: int32, d: int32) {
    requires p + a == q + b;
    requires to_integer(c) - to_integer(a) == to_integer(d) - to_integer(b);
    ensures p + c == q + d;
}

theorem float64_pointer_add_associate_int32(p: double*, i: int32, j: int32) {
    requires defined(i + j);
    ensures (p + i) + j == p + (i + j) by {
        apply(integer::int32_add_to_integer(i, j));
        have (p + i) + 0 == p + i by close();
        have to_integer(j) - 0 == to_integer(i + j) - to_integer(i) by {
            rewrite(to_integer(i + j), to_integer(i) + to_integer(j));
            close();
        }
        apply(integer::float64_pointer_translate_int32(p + i, p, 0, i, j, i + j));
    }
}

axiom float64_pointer_translate_uint64(p: double*, q: double*, a: uint64, b: uint64, c: uint64, d: uint64) {
    requires p + a == q + b;
    requires to_integer(c) - to_integer(a) == to_integer(d) - to_integer(b);
    ensures p + c == q + d;
}

theorem float64_pointer_add_associate_uint64(p: double*, i: uint64, j: uint64) {
    requires to_integer(i) + to_integer(j) <= 18446744073709551615;
    ensures (p + i) + j == p + (i + j) by {
        apply(integer::uint64_add_to_integer(i, j));
        have (p + i) + 0u64 == p + i by close();
        have to_integer(j) - 0 == to_integer(i + j) - to_integer(i) by {
            rewrite(to_integer(i + j), to_integer(i) + to_integer(j));
            close();
        }
        apply(integer::float64_pointer_translate_uint64(p + i, p, 0u64, i, j, i + j));
    }
}
