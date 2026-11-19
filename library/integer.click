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
    ensures (a & 0u64) == 0u64 by known();
}
theorem uint64_or_zero(a: uint64) {
    ensures (a | 0u64) == a by known();
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
        apply(integer::uint64_and_associate(base, large, small)) using {};
        apply(integer::uint64_and_commute(0u64, small)) using {};
        rewrite(small, large & small);
        rewrite(base & (large & small), (base & large) & small);
        rewrite(base & large, 0u64);
        rewrite(0u64 & small, small & 0u64);
        known();
    }
}

theorem uint64_or_masked(base: uint64, tag: uint64, mask: uint64) {
    requires (base & mask) == 0u64;
    ensures (base | (tag & mask)) == ((base + (tag & mask)) as uint64) by {
        have (base & (tag & mask)) == 0u64 by {
            apply(integer::uint64_and_commute(tag, mask)) using {};
            apply(integer::uint64_and_associate(base, mask, tag)) using {};
            apply(integer::uint64_and_commute(0u64, tag)) using {};
            rewrite(tag & mask, mask & tag);
            rewrite(base & (mask & tag), (base & mask) & tag);
            rewrite(base & mask, 0u64);
            rewrite(0u64 & tag, tag & 0u64);
            known();
        }
        apply(integer::uint64_or_disjoint(base, tag & mask)) using { (base & (tag & mask)) == 0u64; };
    }
}

// Address observations respect element offsets independently of memory contents.
axiom uint8_pointer_add_address_int32(p: uint8*, index: int32) {
    ensures address(p + index) == ((address(p) + (index as uint64) * 1u64) as uint64);
}
axiom uint8_pointer_add_address_int64(p: uint8*, index: int64) {
    ensures address(p + index) == ((address(p) + (index as uint64) * 1u64) as uint64);
}
axiom int8_pointer_add_address_int32(p: int8*, index: int32) {
    ensures address(p + index) == ((address(p) + (index as uint64) * 1u64) as uint64);
}
axiom int8_pointer_add_address_int64(p: int8*, index: int64) {
    ensures address(p + index) == ((address(p) + (index as uint64) * 1u64) as uint64);
}
axiom uint16_pointer_add_address_int32(p: uint16*, index: int32) {
    ensures address(p + index) == ((address(p) + (index as uint64) * 2u64) as uint64);
}
axiom uint16_pointer_add_address_int64(p: uint16*, index: int64) {
    ensures address(p + index) == ((address(p) + (index as uint64) * 2u64) as uint64);
}
axiom int16_pointer_add_address_int32(p: int16*, index: int32) {
    ensures address(p + index) == ((address(p) + (index as uint64) * 2u64) as uint64);
}
axiom int16_pointer_add_address_int64(p: int16*, index: int64) {
    ensures address(p + index) == ((address(p) + (index as uint64) * 2u64) as uint64);
}
axiom uint32_pointer_add_address_int32(p: uint32*, index: int32) {
    ensures address(p + index) == ((address(p) + (index as uint64) * 4u64) as uint64);
}
axiom uint32_pointer_add_address_int64(p: uint32*, index: int64) {
    ensures address(p + index) == ((address(p) + (index as uint64) * 4u64) as uint64);
}
axiom int32_pointer_add_address_int32(p: int32*, index: int32) {
    ensures address(p + index) == ((address(p) + (index as uint64) * 4u64) as uint64);
}
axiom int32_pointer_add_address_int64(p: int32*, index: int64) {
    ensures address(p + index) == ((address(p) + (index as uint64) * 4u64) as uint64);
}
axiom uint64_pointer_add_address_int32(p: uint64*, index: int32) {
    ensures address(p + index) == ((address(p) + (index as uint64) * 8u64) as uint64);
}
axiom uint64_pointer_add_address_int64(p: uint64*, index: int64) {
    ensures address(p + index) == ((address(p) + (index as uint64) * 8u64) as uint64);
}
axiom int64_pointer_add_address_int32(p: int64*, index: int32) {
    ensures address(p + index) == ((address(p) + (index as uint64) * 8u64) as uint64);
}
axiom int64_pointer_add_address_int64(p: int64*, index: int64) {
    ensures address(p + index) == ((address(p) + (index as uint64) * 8u64) as uint64);
}
axiom float32_pointer_add_address_int32(p: float*, index: int32) {
    ensures address(p + index) == ((address(p) + (index as uint64) * 4u64) as uint64);
}
axiom float32_pointer_add_address_int64(p: float*, index: int64) {
    ensures address(p + index) == ((address(p) + (index as uint64) * 4u64) as uint64);
}
axiom float64_pointer_add_address_int32(p: double*, index: int32) {
    ensures address(p + index) == ((address(p) + (index as uint64) * 8u64) as uint64);
}
axiom float64_pointer_add_address_int64(p: double*, index: int64) {
    ensures address(p + index) == ((address(p) + (index as uint64) * 8u64) as uint64);
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
        known();
    }
}

theorem negate_as_product(a: Integer) {
    ensures -a == -1 * a by {
        apply(integer::multiply_negate(a, 1));
        apply(integer::multiply_commutative(-1, a));
        have a * 1 == a by known();
        known();
    }
}

theorem multiply_swap_front(a: Integer, b: Integer, c: Integer) {
    ensures a * (b * c) == b * (a * c) by {
        apply(integer::multiply_associative(a, b, c));
        apply(integer::multiply_commutative(a, b));
        apply(integer::multiply_associative(b, a, c));
        known();
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
            known();
        } else {
            have b <= a by { known(); }
            have a + 1 + b <= b + a by {
                apply(integer::add_le(a + 1, b, b, a)) using { a + 1 <= b; b <= a; };
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
            known();
        } else {
            have b <= a by { known(); }
            have a == b by {
                apply(integer::le_antisymmetric(a, b)) using { a <= b; b <= a; };
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
    ensures c <= d by { rewrite(c, a); rewrite(d, b); known(); }
}

theorem equal_substitute(a: Integer, b: Integer, c: Integer, d: Integer) {
    requires a == b;
    requires c == a;
    requires d == b;
    ensures c == d by { rewrite(c, a); rewrite(d, b); known(); }
}

theorem le_difference(a:Integer,b:Integer,value:Integer) {
 requires a<=b;
 requires value==a-b;
 ensures value<=0 by {
  have a + -b <= b + -b by {
   apply(click::integer::add_le(a,b,-b,-b)) using {a<=b;-b<=-b;};
  }
  have value == a + -b by { rewrite(value,a-b); known(); }
  have 0 == b + -b by known();
  apply(click::integer::le_substitute(a + -b,b + -b,value,0)) using {a + -b <= b + -b; value==a + -b;0==b + -b;};
 }
}
theorem difference_le(a:Integer,b:Integer,value:Integer) {
 requires value<=0;
 requires value==a-b;
 ensures a<=b by {
  have value + b <= 0 + b by {
   apply(click::integer::add_le(value,0,b,b)) using {value<=0;b<=b;};
  }
  have a == value + b by { rewrite(value,a-b); known(); }
  have b == 0 + b by known();
  apply(click::integer::le_substitute(value+b,0+b,a,b)) using {value+b<=0+b;a==value+b;b==0+b;};
 }
}

theorem equal_difference(a: Integer, b: Integer) {
    requires a == b;
    ensures a - b == 0 by { rewrite(a, b); known(); }
}

theorem equal_add(a: Integer, b: Integer, c: Integer, d: Integer) {
    requires a == b;
    requires c == d;
    ensures a + c == b + d by { rewrite(a, b); rewrite(c, d); known(); }
}

theorem equal_multiply(a: Integer, b: Integer, factor: Integer) {
    requires a == b;
    ensures a * factor == b * factor by { rewrite(a, b); known(); }
}

theorem equal_negate(a: Integer, b: Integer) {
    requires a == b;
    ensures -a == -b by {
        rewrite(a, b);
        known();
    }
}

theorem equal_le(a: Integer, b: Integer) {
    requires a == b;
    ensures a <= b by { rewrite(a, b); known(); }
}

// No nonnegativity assumption on the remainder is needed for this upper
// bound. The strict upper bound and positive divisor are both essential.
axiom round_down_le(value: Integer, bound: Integer, divisor: Integer, remainder: Integer) {
    requires 0 < divisor;
    requires remainder < divisor;
    requires value * divisor <= bound * divisor + remainder;
    ensures value <= bound;
}

theorem int32_increment_upper_bound(value: int32, upper: int32) {
    requires value < upper;

    ensures to_integer(value + 1) <= to_integer(upper) by {
        have to_integer((upper as int32)) <= to_integer((2147483647 as int32)) by {
            normalize() using {};
        }
        have (to_integer(((value as int32) as int32)) + to_integer((upper as int32))) < (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32))) by {
            have (to_integer(((value as int32) as int32)) + to_integer((upper as int32))) < (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32))) by {
                have (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((upper as int32) as int32) as int32))) + 1) <= 0 by {
                    have to_integer((((value as int32) as int32) as int32)) < to_integer((((upper as int32) as int32) as int32)) by {
                        normalize() using {
                            ((value as int32) as int32) < ((upper as int32) as int32);
                        };
                    }
                    have (to_integer((((value as int32) as int32) as int32)) + 1) <= to_integer((((upper as int32) as int32) as int32)) by {
                        apply(click::integer::lt_step_le(to_integer((((value as int32) as int32) as int32)), to_integer((((upper as int32) as int32) as int32)))) using {
                            to_integer((((value as int32) as int32) as int32)) < to_integer((((upper as
                                int32) as int32) as int32));
                        };
                    }
                    have (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((upper as int32) as int32) as int32))) + 1) == ((to_integer((((value as int32) as int32) as int32)) + 1) - to_integer((((upper as int32) as int32) as int32))) by {
                        normalize();
                    }
                    apply(click::integer::le_difference((to_integer((((value as int32) as int32) as int32)) + 1), to_integer((((upper as int32) as int32) as int32)), (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((upper as int32) as int32) as int32))) + 1))) using {
                        (to_integer((((value as int32) as int32) as int32)) + 1) <= to_integer((((upper
                            as int32) as int32) as int32));
                        (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((upper
                            as int32) as int32) as int32))) + 1) == ((to_integer((((value as int32) as
                            int32) as int32)) + 1) - to_integer((((upper as int32) as int32) as
                            int32)));
                    };
                }
                have (to_integer((((upper as int32) as int32) as int32)) + -2147483647) <= 0 by {
                    have (to_integer((((upper as int32) as int32) as int32)) + -2147483647) == (to_integer((upper as int32)) - to_integer((2147483647 as int32))) by {
                        normalize();
                    }
                    apply(click::integer::le_difference(to_integer((upper as int32)), to_integer((2147483647 as int32)), (to_integer((((upper as int32) as int32) as int32)) + -2147483647))) using {
                        to_integer((upper as int32)) <= to_integer((2147483647 as int32));
                        (to_integer((((upper as int32) as int32) as int32)) + -2147483647) ==
                            (to_integer((upper as int32)) - to_integer((2147483647 as int32)));
                    };
                }
                have (to_integer((((value as int32) as int32) as int32)) + -2147483646) <= 0 by {
                    have (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((upper as int32) as int32) as int32))) + 1 + (to_integer((((upper as int32) as int32) as int32)) + -2147483647)) <= (0 + 0) by {
                        apply(click::integer::add_le((to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((upper as int32) as int32) as int32))) + 1), 0, (to_integer((((upper as int32) as int32) as int32)) + -2147483647), 0)) using {
                            (to_integer((((value as int32) as int32) as int32)) + (-1 *
                                to_integer((((upper as int32) as int32) as int32))) + 1) <= 0;
                            (to_integer((((upper as int32) as int32) as int32)) + -2147483647) <= 0;
                        };
                    }
                    have (to_integer((((value as int32) as int32) as int32)) + -2147483646) == (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((upper as int32) as int32) as int32))) + 1 + (to_integer((((upper as int32) as int32) as int32)) + -2147483647)) by {
                        normalize();
                    }
                    have (let integer_value: Integer = 0; integer_value) == (0 + 0) by {
                        normalize();
                    }
                    apply(click::integer::le_substitute((to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((upper as int32) as int32) as int32))) + 1 + (to_integer((((upper as int32) as int32) as int32)) + -2147483647)), (0 + 0), (to_integer((((value as int32) as int32) as int32)) + -2147483646), 0)) using {
                        (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((upper
                            as int32) as int32) as int32))) + 1 + (to_integer((((upper as int32) as
                            int32) as int32)) + -2147483647)) <= (0 + 0);
                        (to_integer((((value as int32) as int32) as int32)) + -2147483646) ==
                            (to_integer((((value as int32) as int32) as int32)) + (-1 *
                            to_integer((((upper as int32) as int32) as int32))) + 1 +
                            (to_integer((((upper as int32) as int32) as int32)) + -2147483647));
                        (let integer_value: Integer = 0; integer_value) == (0 + 0);
                    };
                }
                have (to_integer((((value as int32) as int32) as int32)) + -2147483646) == ((to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + 1) - (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32)))) by {
                    normalize();
                }
                apply(click::integer::difference_le((to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + 1), (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32))), (to_integer((((value as int32) as int32) as int32)) + -2147483646))) using {
                    (to_integer((((value as int32) as int32) as int32)) + -2147483646) <= 0;
                    (to_integer((((value as int32) as int32) as int32)) + -2147483646) ==
                        ((to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + 1) -
                        (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32))));
                };
                apply(click::integer::step_le_lt((to_integer(((value as int32) as int32)) + to_integer((upper as int32))), (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32))))) using {
                    (to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + 1) <=
                        (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32)));
                };
            }
            normalize() using {
                (to_integer(((value as int32) as int32)) + to_integer((upper as int32))) <
                    (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32)));
            };
        }
        have -2147483648 <= to_integer((value as int32)) by {
            normalize() using {
                (to_integer(((value as int32) as int32)) + to_integer((upper as int32))) <
                    (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32)));
            };
        }
        have to_integer((value as int32)) <= 2147483646 by {
            have to_integer((value as int32)) <= 2147483646 by {
                have (to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + (-1 * (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32)))) + 1) <= 0 by {
                    have (to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + 1) <= (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32))) by {
                        apply(click::integer::lt_step_le((to_integer(((value as int32) as int32)) + to_integer((upper as int32))), (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32))))) using {
                            (to_integer(((value as int32) as int32)) + to_integer((upper as int32))) <
                                (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as
                                int32)));
                        };
                    }
                    have (to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + (-1 * (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32)))) + 1) == ((to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + 1) - (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32)))) by {
                        normalize();
                    }
                    apply(click::integer::le_difference((to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + 1), (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32))), (to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + (-1 * (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32)))) + 1))) using {
                        (to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + 1) <=
                            (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as
                            int32)));
                        (to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + (-1 *
                            (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as
                            int32)))) + 1) == ((to_integer(((value as int32) as int32)) +
                            to_integer((upper as int32)) + 1) - (to_integer(((upper as int32) as int32))
                            + to_integer((2147483647 as int32))));
                    };
                }
                have (to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + (-1 * (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32)))) + 1) == (to_integer((value as int32)) - 2147483646) by {
                    normalize();
                }
                apply(click::integer::difference_le(to_integer((value as int32)), 2147483646, (to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + (-1 * (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32)))) + 1))) using {
                    (to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + (-1 *
                        (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32)))) +
                        1) <= 0;
                    (to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + (-1 *
                        (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32)))) +
                        1) == (to_integer((value as int32)) - 2147483646);
                };
            }
            normalize() using {
                to_integer((value as int32)) <= 2147483646;
            };
        }
        have 1 <= to_integer((1 as int32)) by {
            normalize() using {};
        }
        have to_integer((1 as int32)) <= 1 by {
            normalize() using {};
        }
        have -2147483648 <= (to_integer((value as int32)) + to_integer((1 as int32))) by {
            have -2147483648 <= (to_integer((value as int32)) + to_integer((1 as int32))) by {
                have ((-1 * to_integer((value as int32))) + -to_integer(2147483648u64)) <= 0 by {
                    have ((-1 * to_integer((value as int32))) + -to_integer(2147483648u64)) == (-2147483648 - to_integer((value as int32))) by {
                        normalize();
                    }
                    apply(click::integer::le_difference(-2147483648, to_integer((value as int32)), ((-1 * to_integer((value as int32))) + -to_integer(2147483648u64)))) using {
                        -2147483648 <= to_integer((value as int32));
                        ((-1 * to_integer((value as int32))) + -to_integer(2147483648u64)) ==
                            (-2147483648 - to_integer((value as int32)));
                    };
                }
                have (let integer_constant: Integer = -1; integer_constant) <= 0 by {
                    normalize();
                }
                have ((-1 * to_integer((value as int32))) + -to_integer(2147483649u64)) <= 0 by {
                    have ((-1 * to_integer((value as int32))) + -to_integer(2147483648u64) + (let integer_constant: Integer = -1; integer_constant)) <= (0 + 0) by {
                        apply(click::integer::add_le(((-1 * to_integer((value as int32))) + -to_integer(2147483648u64)), 0, (let integer_constant: Integer = -1; integer_constant), 0)) using {
                            ((-1 * to_integer((value as int32))) + -to_integer(2147483648u64)) <= 0;
                            (let integer_constant: Integer = -1; integer_constant) <= 0;
                        };
                    }
                    have ((-1 * to_integer((value as int32))) + -to_integer(2147483649u64)) == ((-1 * to_integer((value as int32))) + -to_integer(2147483648u64) + (let integer_constant: Integer = -1; integer_constant)) by {
                        normalize();
                    }
                    have (let integer_value: Integer = 0; integer_value) == (0 + 0) by {
                        normalize();
                    }
                    apply(click::integer::le_substitute(((-1 * to_integer((value as int32))) + -to_integer(2147483648u64) + (let integer_constant: Integer = -1; integer_constant)), (0 + 0), ((-1 * to_integer((value as int32))) + -to_integer(2147483649u64)), 0)) using {
                        ((-1 * to_integer((value as int32))) + -to_integer(2147483648u64) + (let
                            integer_constant: Integer = -1; integer_constant)) <= (0 + 0);
                        ((-1 * to_integer((value as int32))) + -to_integer(2147483649u64)) == ((-1 *
                            to_integer((value as int32))) + -to_integer(2147483648u64) + (let
                            integer_constant: Integer = -1; integer_constant));
                        (let integer_value: Integer = 0; integer_value) == (0 + 0);
                    };
                }
                have ((-1 * to_integer((value as int32))) + -to_integer(2147483649u64)) == (-2147483648 - (to_integer((value as int32)) + to_integer((1 as int32)))) by {
                    normalize();
                }
                apply(click::integer::difference_le(-2147483648, (to_integer((value as int32)) + to_integer((1 as int32))), ((-1 * to_integer((value as int32))) + -to_integer(2147483649u64)))) using {
                    ((-1 * to_integer((value as int32))) + -to_integer(2147483649u64)) <= 0;
                    ((-1 * to_integer((value as int32))) + -to_integer(2147483649u64)) == (-2147483648 -
                        (to_integer((value as int32)) + to_integer((1 as int32))));
                };
            }
            normalize() using {
                -2147483648 <= (to_integer((value as int32)) + to_integer((1 as int32)));
            };
        }
        have (to_integer((value as int32)) + to_integer((1 as int32))) <= 2147483647 by {
            have (to_integer((value as int32)) + to_integer((1 as int32))) <= 2147483647 by {
                have (to_integer((value as int32)) + -2147483646) <= 0 by {
                    have (to_integer((value as int32)) + -2147483646) == (to_integer((value as int32)) - 2147483646) by {
                        normalize();
                    }
                    apply(click::integer::le_difference(to_integer((value as int32)), 2147483646, (to_integer((value as int32)) + -2147483646))) using {
                        to_integer((value as int32)) <= 2147483646;
                        (to_integer((value as int32)) + -2147483646) == (to_integer((value as int32)) -
                            2147483646);
                    };
                }
                have (to_integer((value as int32)) + -2147483646) == ((to_integer((value as int32)) + to_integer((1 as int32))) - 2147483647) by {
                    normalize();
                }
                apply(click::integer::difference_le((to_integer((value as int32)) + to_integer((1 as int32))), 2147483647, (to_integer((value as int32)) + -2147483646))) using {
                    (to_integer((value as int32)) + -2147483646) <= 0;
                    (to_integer((value as int32)) + -2147483646) == ((to_integer((value as int32)) +
                        to_integer((1 as int32))) - 2147483647);
                };
            }
            normalize() using {
                (to_integer((value as int32)) + to_integer((1 as int32))) <= 2147483647;
            };
        }
        have defined((value + 1)) by {
            known();
        }
        have to_integer(((value + 1) as int32)) == (to_integer((value as int32)) + to_integer((1 as int32))) by {
            normalize() using {
                -2147483648 <= (to_integer((value as int32)) + to_integer((1 as int32)));
                (to_integer((value as int32)) + to_integer((1 as int32))) <= 2147483647;
            };
        }
        have -2147483647 <= to_integer(((value + 1) as int32)) by {
            normalize() using {
                -2147483648 <= to_integer((value as int32));
                to_integer((value as int32)) <= 2147483646;
                1 <= to_integer((1 as int32));
                to_integer((1 as int32)) <= 1;
                to_integer(((value + 1) as int32)) == (to_integer((value as int32)) + to_integer((1 as
                    int32)));
            };
        }
        have to_integer(((value + 1) as int32)) <= 2147483647 by {
            normalize() using {
                -2147483648 <= to_integer((value as int32));
                to_integer((value as int32)) <= 2147483646;
                1 <= to_integer((1 as int32));
                to_integer((1 as int32)) <= 1;
                to_integer(((value + 1) as int32)) == (to_integer((value as int32)) + to_integer((1 as
                    int32)));
            };
        }
        have ((value + 1) as int32) <= (upper as int32) by {
            have defined(((value + 1) as int32)) by {
                known();
            }
            have defined((value + 1)) by {
                known();
            }
            have defined(old(((value + 1) as int32))) by {
                known();
            }
            have defined(old((value + 1))) by {
                known();
            }
            have to_integer((((value + 1) as int32) as int32)) <= to_integer(((upper as int32) as int32)) by {
                have (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((upper as int32) as int32) as int32))) + 1) <= 0 by {
                    have to_integer((((value as int32) as int32) as int32)) < to_integer((((upper as int32) as int32) as int32)) by {
                        normalize() using {
                            ((value as int32) as int32) < ((upper as int32) as int32);
                        };
                    }
                    have (to_integer((((value as int32) as int32) as int32)) + 1) <= to_integer((((upper as int32) as int32) as int32)) by {
                        apply(click::integer::lt_step_le(to_integer((((value as int32) as int32) as int32)), to_integer((((upper as int32) as int32) as int32)))) using {
                            to_integer((((value as int32) as int32) as int32)) < to_integer((((upper as
                                int32) as int32) as int32));
                            defined(((value + 1) as int32));
                            defined((value + 1));
                            defined(old(((value + 1) as int32)));
                            defined(old((value + 1)));
                        };
                    }
                    have (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((upper as int32) as int32) as int32))) + 1) == ((to_integer((((value as int32) as int32) as int32)) + 1) - to_integer((((upper as int32) as int32) as int32))) by {
                        normalize();
                    }
                    apply(click::integer::le_difference((to_integer((((value as int32) as int32) as int32)) + 1), to_integer((((upper as int32) as int32) as int32)), (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((upper as int32) as int32) as int32))) + 1))) using {
                        (to_integer((((value as int32) as int32) as int32)) + 1) <= to_integer((((upper
                            as int32) as int32) as int32));
                        (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((upper
                            as int32) as int32) as int32))) + 1) == ((to_integer((((value as int32) as
                            int32) as int32)) + 1) - to_integer((((upper as int32) as int32) as
                            int32)));
                        defined(((value + 1) as int32));
                        defined((value + 1));
                        defined(old(((value + 1) as int32)));
                        defined(old((value + 1)));
                    };
                }
                have ((-1 * (to_integer((value as int32)) + to_integer((1 as int32)))) + to_integer(((value + 1) as int32))) == 0 by {
                    have (to_integer(((value + 1) as int32)) - (to_integer((value as int32)) + to_integer((1 as int32)))) == 0 by {
                        apply(click::integer::equal_difference(to_integer(((value + 1) as int32)), (to_integer((value as int32)) + to_integer((1 as int32))))) using {
                            to_integer(((value + 1) as int32)) == (to_integer((value as int32)) +
                                to_integer((1 as int32)));
                            defined(((value + 1) as int32));
                            defined((value + 1));
                            defined(old(((value + 1) as int32)));
                            defined(old((value + 1)));
                        };
                    }
                    have ((-1 * (to_integer((value as int32)) + to_integer((1 as int32)))) + to_integer(((value + 1) as int32))) == (to_integer(((value + 1) as int32)) - (to_integer((value as int32)) + to_integer((1 as int32)))) by {
                        normalize();
                    }
                    apply(click::integer::equal_substitute((to_integer(((value + 1) as int32)) - (to_integer((value as int32)) + to_integer((1 as int32)))), 0, ((-1 * (to_integer((value as int32)) + to_integer((1 as int32)))) + to_integer(((value + 1) as int32))), 0)) using {
                        (to_integer(((value + 1) as int32)) - (to_integer((value as int32)) +
                            to_integer((1 as int32)))) == 0;
                        ((-1 * (to_integer((value as int32)) + to_integer((1 as int32)))) +
                            to_integer(((value + 1) as int32))) == (to_integer(((value + 1) as int32)) -
                            (to_integer((value as int32)) + to_integer((1 as int32))));
                        (let integer_value: Integer = 0; integer_value) == 0;
                        defined(((value + 1) as int32));
                        defined((value + 1));
                        defined(old(((value + 1) as int32)));
                        defined(old((value + 1)));
                    };
                }
                have ((-1 * (to_integer((value as int32)) + to_integer((1 as int32)))) + to_integer(((value + 1) as int32))) <= 0 by {
                    apply(click::integer::equal_le(((-1 * (to_integer((value as int32)) + to_integer((1 as int32)))) + to_integer(((value + 1) as int32))), 0)) using {
                        ((-1 * (to_integer((value as int32)) + to_integer((1 as int32)))) +
                            to_integer(((value + 1) as int32))) == 0;
                        defined(((value + 1) as int32));
                        defined((value + 1));
                        defined(old(((value + 1) as int32)));
                        defined(old((value + 1)));
                    };
                }
                have (to_integer((((value as int32) as int32) as int32)) + (-1 * (to_integer((value as int32)) + to_integer((1 as int32)))) + (-1 * to_integer((((upper as int32) as int32) as int32))) + to_integer(((value + 1) as int32)) + 1) <= 0 by {
                    have (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((upper as int32) as int32) as int32))) + 1 + ((-1 * (to_integer((value as int32)) + to_integer((1 as int32)))) + to_integer(((value + 1) as int32)))) <= (0 + 0) by {
                        apply(click::integer::add_le((to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((upper as int32) as int32) as int32))) + 1), 0, ((-1 * (to_integer((value as int32)) + to_integer((1 as int32)))) + to_integer(((value + 1) as int32))), 0)) using {
                            (to_integer((((value as int32) as int32) as int32)) + (-1 *
                                to_integer((((upper as int32) as int32) as int32))) + 1) <= 0;
                            ((-1 * (to_integer((value as int32)) + to_integer((1 as int32)))) +
                                to_integer(((value + 1) as int32))) <= 0;
                            defined(((value + 1) as int32));
                            defined((value + 1));
                            defined(old(((value + 1) as int32)));
                            defined(old((value + 1)));
                        };
                    }
                    have (to_integer((((value as int32) as int32) as int32)) + (-1 * (to_integer((value as int32)) + to_integer((1 as int32)))) + (-1 * to_integer((((upper as int32) as int32) as int32))) + to_integer(((value + 1) as int32)) + 1) == (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((upper as int32) as int32) as int32))) + 1 + ((-1 * (to_integer((value as int32)) + to_integer((1 as int32)))) + to_integer(((value + 1) as int32)))) by {
                        normalize();
                    }
                    have (let integer_value: Integer = 0; integer_value) == (0 + 0) by {
                        normalize();
                    }
                    apply(click::integer::le_substitute((to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((upper as int32) as int32) as int32))) + 1 + ((-1 * (to_integer((value as int32)) + to_integer((1 as int32)))) + to_integer(((value + 1) as int32)))), (0 + 0), (to_integer((((value as int32) as int32) as int32)) + (-1 * (to_integer((value as int32)) + to_integer((1 as int32)))) + (-1 * to_integer((((upper as int32) as int32) as int32))) + to_integer(((value + 1) as int32)) + 1), 0)) using {
                        (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((upper
                            as int32) as int32) as int32))) + 1 + ((-1 * (to_integer((value as int32)) +
                            to_integer((1 as int32)))) + to_integer(((value + 1) as int32)))) <= (0 +
                            0);
                        (to_integer((((value as int32) as int32) as int32)) + (-1 * (to_integer((value
                            as int32)) + to_integer((1 as int32)))) + (-1 * to_integer((((upper as
                            int32) as int32) as int32))) + to_integer(((value + 1) as int32)) + 1) ==
                            (to_integer((((value as int32) as int32) as int32)) + (-1 *
                            to_integer((((upper as int32) as int32) as int32))) + 1 + ((-1 *
                            (to_integer((value as int32)) + to_integer((1 as int32)))) +
                            to_integer(((value + 1) as int32))));
                        (let integer_value: Integer = 0; integer_value) == (0 + 0);
                        defined(((value + 1) as int32));
                        defined((value + 1));
                        defined(old(((value + 1) as int32)));
                        defined(old((value + 1)));
                    };
                }
                have (to_integer((((value as int32) as int32) as int32)) + (-1 * (to_integer((value as int32)) + to_integer((1 as int32)))) + (-1 * to_integer((((upper as int32) as int32) as int32))) + to_integer(((value + 1) as int32)) + 1) == (to_integer((((value + 1) as int32) as int32)) - to_integer(((upper as int32) as int32))) by {
                    normalize();
                }
                apply(click::integer::difference_le(to_integer((((value + 1) as int32) as int32)), to_integer(((upper as int32) as int32)), (to_integer((((value as int32) as int32) as int32)) + (-1 * (to_integer((value as int32)) + to_integer((1 as int32)))) + (-1 * to_integer((((upper as int32) as int32) as int32))) + to_integer(((value + 1) as int32)) + 1))) using {
                    (to_integer((((value as int32) as int32) as int32)) + (-1 * (to_integer((value as
                        int32)) + to_integer((1 as int32)))) + (-1 * to_integer((((upper as int32) as
                        int32) as int32))) + to_integer(((value + 1) as int32)) + 1) <= 0;
                    (to_integer((((value as int32) as int32) as int32)) + (-1 * (to_integer((value as
                        int32)) + to_integer((1 as int32)))) + (-1 * to_integer((((upper as int32) as
                        int32) as int32))) + to_integer(((value + 1) as int32)) + 1) ==
                        (to_integer((((value + 1) as int32) as int32)) - to_integer(((upper as int32) as
                        int32)));
                    defined(((value + 1) as int32));
                    defined((value + 1));
                    defined(old(((value + 1) as int32)));
                    defined(old((value + 1)));
                };
            }
            normalize() using {
                to_integer((((value + 1) as int32) as int32)) <= to_integer(((upper as int32) as
                    int32));
            };
        }
        have to_integer((value + 1)) <= to_integer(upper) by {
            normalize() using {
                ((value + 1) as int32) <= (upper as int32);
                to_integer(((value + 1) as int32)) == (to_integer((value as int32)) + to_integer((1 as
                    int32)));
            };
        }
        known();
    }
}

theorem int32_increment_strictly_increases(value: int32, upper: int32) {
    requires value < upper;

    ensures to_integer(value) < to_integer(value + 1) by {
        have to_integer((upper as int32)) <= to_integer((2147483647 as int32)) by {
            normalize() using {};
        }
        have (to_integer(((value as int32) as int32)) + to_integer((upper as int32))) < (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32))) by {
            have (to_integer(((value as int32) as int32)) + to_integer((upper as int32))) < (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32))) by {
                have (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((upper as int32) as int32) as int32))) + 1) <= 0 by {
                    have to_integer((((value as int32) as int32) as int32)) < to_integer((((upper as int32) as int32) as int32)) by {
                        normalize() using {
                            ((value as int32) as int32) < ((upper as int32) as int32);
                        };
                    }
                    have (to_integer((((value as int32) as int32) as int32)) + 1) <= to_integer((((upper as int32) as int32) as int32)) by {
                        apply(click::integer::lt_step_le(to_integer((((value as int32) as int32) as int32)), to_integer((((upper as int32) as int32) as int32)))) using {
                            to_integer((((value as int32) as int32) as int32)) < to_integer((((upper as
                                int32) as int32) as int32));
                        };
                    }
                    have (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((upper as int32) as int32) as int32))) + 1) == ((to_integer((((value as int32) as int32) as int32)) + 1) - to_integer((((upper as int32) as int32) as int32))) by {
                        normalize();
                    }
                    apply(click::integer::le_difference((to_integer((((value as int32) as int32) as int32)) + 1), to_integer((((upper as int32) as int32) as int32)), (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((upper as int32) as int32) as int32))) + 1))) using {
                        (to_integer((((value as int32) as int32) as int32)) + 1) <= to_integer((((upper
                            as int32) as int32) as int32));
                        (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((upper
                            as int32) as int32) as int32))) + 1) == ((to_integer((((value as int32) as
                            int32) as int32)) + 1) - to_integer((((upper as int32) as int32) as
                            int32)));
                    };
                }
                have (to_integer((((upper as int32) as int32) as int32)) + -2147483647) <= 0 by {
                    have (to_integer((((upper as int32) as int32) as int32)) + -2147483647) == (to_integer((upper as int32)) - to_integer((2147483647 as int32))) by {
                        normalize();
                    }
                    apply(click::integer::le_difference(to_integer((upper as int32)), to_integer((2147483647 as int32)), (to_integer((((upper as int32) as int32) as int32)) + -2147483647))) using {
                        to_integer((upper as int32)) <= to_integer((2147483647 as int32));
                        (to_integer((((upper as int32) as int32) as int32)) + -2147483647) ==
                            (to_integer((upper as int32)) - to_integer((2147483647 as int32)));
                    };
                }
                have (to_integer((((value as int32) as int32) as int32)) + -2147483646) <= 0 by {
                    have (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((upper as int32) as int32) as int32))) + 1 + (to_integer((((upper as int32) as int32) as int32)) + -2147483647)) <= (0 + 0) by {
                        apply(click::integer::add_le((to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((upper as int32) as int32) as int32))) + 1), 0, (to_integer((((upper as int32) as int32) as int32)) + -2147483647), 0)) using {
                            (to_integer((((value as int32) as int32) as int32)) + (-1 *
                                to_integer((((upper as int32) as int32) as int32))) + 1) <= 0;
                            (to_integer((((upper as int32) as int32) as int32)) + -2147483647) <= 0;
                        };
                    }
                    have (to_integer((((value as int32) as int32) as int32)) + -2147483646) == (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((upper as int32) as int32) as int32))) + 1 + (to_integer((((upper as int32) as int32) as int32)) + -2147483647)) by {
                        normalize();
                    }
                    have (let integer_value: Integer = 0; integer_value) == (0 + 0) by {
                        normalize();
                    }
                    apply(click::integer::le_substitute((to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((upper as int32) as int32) as int32))) + 1 + (to_integer((((upper as int32) as int32) as int32)) + -2147483647)), (0 + 0), (to_integer((((value as int32) as int32) as int32)) + -2147483646), 0)) using {
                        (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((upper
                            as int32) as int32) as int32))) + 1 + (to_integer((((upper as int32) as
                            int32) as int32)) + -2147483647)) <= (0 + 0);
                        (to_integer((((value as int32) as int32) as int32)) + -2147483646) ==
                            (to_integer((((value as int32) as int32) as int32)) + (-1 *
                            to_integer((((upper as int32) as int32) as int32))) + 1 +
                            (to_integer((((upper as int32) as int32) as int32)) + -2147483647));
                        (let integer_value: Integer = 0; integer_value) == (0 + 0);
                    };
                }
                have (to_integer((((value as int32) as int32) as int32)) + -2147483646) == ((to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + 1) - (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32)))) by {
                    normalize();
                }
                apply(click::integer::difference_le((to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + 1), (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32))), (to_integer((((value as int32) as int32) as int32)) + -2147483646))) using {
                    (to_integer((((value as int32) as int32) as int32)) + -2147483646) <= 0;
                    (to_integer((((value as int32) as int32) as int32)) + -2147483646) ==
                        ((to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + 1) -
                        (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32))));
                };
                apply(click::integer::step_le_lt((to_integer(((value as int32) as int32)) + to_integer((upper as int32))), (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32))))) using {
                    (to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + 1) <=
                        (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32)));
                };
            }
            normalize() using {
                (to_integer(((value as int32) as int32)) + to_integer((upper as int32))) <
                    (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32)));
            };
        }
        have -2147483648 <= to_integer((value as int32)) by {
            normalize() using {
                (to_integer(((value as int32) as int32)) + to_integer((upper as int32))) <
                    (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32)));
            };
        }
        have to_integer((value as int32)) <= 2147483646 by {
            have to_integer((value as int32)) <= 2147483646 by {
                have (to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + (-1 * (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32)))) + 1) <= 0 by {
                    have (to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + 1) <= (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32))) by {
                        apply(click::integer::lt_step_le((to_integer(((value as int32) as int32)) + to_integer((upper as int32))), (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32))))) using {
                            (to_integer(((value as int32) as int32)) + to_integer((upper as int32))) <
                                (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as
                                int32)));
                        };
                    }
                    have (to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + (-1 * (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32)))) + 1) == ((to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + 1) - (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32)))) by {
                        normalize();
                    }
                    apply(click::integer::le_difference((to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + 1), (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32))), (to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + (-1 * (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32)))) + 1))) using {
                        (to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + 1) <=
                            (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as
                            int32)));
                        (to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + (-1 *
                            (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as
                            int32)))) + 1) == ((to_integer(((value as int32) as int32)) +
                            to_integer((upper as int32)) + 1) - (to_integer(((upper as int32) as int32))
                            + to_integer((2147483647 as int32))));
                    };
                }
                have (to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + (-1 * (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32)))) + 1) == (to_integer((value as int32)) - 2147483646) by {
                    normalize();
                }
                apply(click::integer::difference_le(to_integer((value as int32)), 2147483646, (to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + (-1 * (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32)))) + 1))) using {
                    (to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + (-1 *
                        (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32)))) +
                        1) <= 0;
                    (to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + (-1 *
                        (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32)))) +
                        1) == (to_integer((value as int32)) - 2147483646);
                };
            }
            normalize() using {
                to_integer((value as int32)) <= 2147483646;
            };
        }
        have 1 <= to_integer((1 as int32)) by {
            normalize() using {};
        }
        have to_integer((1 as int32)) <= 1 by {
            normalize() using {};
        }
        have -2147483648 <= (to_integer((value as int32)) + to_integer((1 as int32))) by {
            have -2147483648 <= (to_integer((value as int32)) + to_integer((1 as int32))) by {
                have ((-1 * to_integer((value as int32))) + -to_integer(2147483648u64)) <= 0 by {
                    have ((-1 * to_integer((value as int32))) + -to_integer(2147483648u64)) == (-2147483648 - to_integer((value as int32))) by {
                        normalize();
                    }
                    apply(click::integer::le_difference(-2147483648, to_integer((value as int32)), ((-1 * to_integer((value as int32))) + -to_integer(2147483648u64)))) using {
                        -2147483648 <= to_integer((value as int32));
                        ((-1 * to_integer((value as int32))) + -to_integer(2147483648u64)) ==
                            (-2147483648 - to_integer((value as int32)));
                    };
                }
                have (let integer_constant: Integer = -1; integer_constant) <= 0 by {
                    normalize();
                }
                have ((-1 * to_integer((value as int32))) + -to_integer(2147483649u64)) <= 0 by {
                    have ((-1 * to_integer((value as int32))) + -to_integer(2147483648u64) + (let integer_constant: Integer = -1; integer_constant)) <= (0 + 0) by {
                        apply(click::integer::add_le(((-1 * to_integer((value as int32))) + -to_integer(2147483648u64)), 0, (let integer_constant: Integer = -1; integer_constant), 0)) using {
                            ((-1 * to_integer((value as int32))) + -to_integer(2147483648u64)) <= 0;
                            (let integer_constant: Integer = -1; integer_constant) <= 0;
                        };
                    }
                    have ((-1 * to_integer((value as int32))) + -to_integer(2147483649u64)) == ((-1 * to_integer((value as int32))) + -to_integer(2147483648u64) + (let integer_constant: Integer = -1; integer_constant)) by {
                        normalize();
                    }
                    have (let integer_value: Integer = 0; integer_value) == (0 + 0) by {
                        normalize();
                    }
                    apply(click::integer::le_substitute(((-1 * to_integer((value as int32))) + -to_integer(2147483648u64) + (let integer_constant: Integer = -1; integer_constant)), (0 + 0), ((-1 * to_integer((value as int32))) + -to_integer(2147483649u64)), 0)) using {
                        ((-1 * to_integer((value as int32))) + -to_integer(2147483648u64) + (let
                            integer_constant: Integer = -1; integer_constant)) <= (0 + 0);
                        ((-1 * to_integer((value as int32))) + -to_integer(2147483649u64)) == ((-1 *
                            to_integer((value as int32))) + -to_integer(2147483648u64) + (let
                            integer_constant: Integer = -1; integer_constant));
                        (let integer_value: Integer = 0; integer_value) == (0 + 0);
                    };
                }
                have ((-1 * to_integer((value as int32))) + -to_integer(2147483649u64)) == (-2147483648 - (to_integer((value as int32)) + to_integer((1 as int32)))) by {
                    normalize();
                }
                apply(click::integer::difference_le(-2147483648, (to_integer((value as int32)) + to_integer((1 as int32))), ((-1 * to_integer((value as int32))) + -to_integer(2147483649u64)))) using {
                    ((-1 * to_integer((value as int32))) + -to_integer(2147483649u64)) <= 0;
                    ((-1 * to_integer((value as int32))) + -to_integer(2147483649u64)) == (-2147483648 -
                        (to_integer((value as int32)) + to_integer((1 as int32))));
                };
            }
            normalize() using {
                -2147483648 <= (to_integer((value as int32)) + to_integer((1 as int32)));
            };
        }
        have (to_integer((value as int32)) + to_integer((1 as int32))) <= 2147483647 by {
            have (to_integer((value as int32)) + to_integer((1 as int32))) <= 2147483647 by {
                have (to_integer((value as int32)) + -2147483646) <= 0 by {
                    have (to_integer((value as int32)) + -2147483646) == (to_integer((value as int32)) - 2147483646) by {
                        normalize();
                    }
                    apply(click::integer::le_difference(to_integer((value as int32)), 2147483646, (to_integer((value as int32)) + -2147483646))) using {
                        to_integer((value as int32)) <= 2147483646;
                        (to_integer((value as int32)) + -2147483646) == (to_integer((value as int32)) -
                            2147483646);
                    };
                }
                have (to_integer((value as int32)) + -2147483646) == ((to_integer((value as int32)) + to_integer((1 as int32))) - 2147483647) by {
                    normalize();
                }
                apply(click::integer::difference_le((to_integer((value as int32)) + to_integer((1 as int32))), 2147483647, (to_integer((value as int32)) + -2147483646))) using {
                    (to_integer((value as int32)) + -2147483646) <= 0;
                    (to_integer((value as int32)) + -2147483646) == ((to_integer((value as int32)) +
                        to_integer((1 as int32))) - 2147483647);
                };
            }
            normalize() using {
                (to_integer((value as int32)) + to_integer((1 as int32))) <= 2147483647;
            };
        }
        have defined((value + 1)) by {
            known();
        }
        have to_integer(((value + 1) as int32)) == (to_integer((value as int32)) + to_integer((1 as int32))) by {
            normalize() using {
                -2147483648 <= (to_integer((value as int32)) + to_integer((1 as int32)));
                (to_integer((value as int32)) + to_integer((1 as int32))) <= 2147483647;
            };
        }
        have -2147483647 <= to_integer(((value + 1) as int32)) by {
            normalize() using {
                -2147483648 <= to_integer((value as int32));
                to_integer((value as int32)) <= 2147483646;
                1 <= to_integer((1 as int32));
                to_integer((1 as int32)) <= 1;
                to_integer(((value + 1) as int32)) == (to_integer((value as int32)) + to_integer((1 as
                    int32)));
            };
        }
        have to_integer(((value + 1) as int32)) <= 2147483647 by {
            normalize() using {
                -2147483648 <= to_integer((value as int32));
                to_integer((value as int32)) <= 2147483646;
                1 <= to_integer((1 as int32));
                to_integer((1 as int32)) <= 1;
                to_integer(((value + 1) as int32)) == (to_integer((value as int32)) + to_integer((1 as
                    int32)));
            };
        }
        have 0 <= 0 by {
            normalize() using {
                to_integer(((value + 1) as int32)) == (to_integer((value as int32)) + to_integer((1 as
                    int32)));
            };
        }
        have (value as int32) < ((value + 1) as int32) by {
            have defined(((value + 1) as int32)) by {
                known();
            }
            have defined((value + 1)) by {
                known();
            }
            have defined(old(((value + 1) as int32))) by {
                known();
            }
            have defined(old((value + 1))) by {
                known();
            }
            have to_integer(((value as int32) as int32)) < to_integer((((value + 1) as int32) as int32)) by {
                have ((-1 * (to_integer((value as int32)) + to_integer((1 as int32)))) + to_integer(((value + 1) as int32))) == 0 by {
                    have (to_integer(((value + 1) as int32)) - (to_integer((value as int32)) + to_integer((1 as int32)))) == 0 by {
                        apply(click::integer::equal_difference(to_integer(((value + 1) as int32)), (to_integer((value as int32)) + to_integer((1 as int32))))) using {
                            to_integer(((value + 1) as int32)) == (to_integer((value as int32)) +
                                to_integer((1 as int32)));
                            defined(((value + 1) as int32));
                            defined((value + 1));
                            defined(old(((value + 1) as int32)));
                            defined(old((value + 1)));
                        };
                    }
                    have ((-1 * (to_integer((value as int32)) + to_integer((1 as int32)))) + to_integer(((value + 1) as int32))) == (to_integer(((value + 1) as int32)) - (to_integer((value as int32)) + to_integer((1 as int32)))) by {
                        normalize();
                    }
                    apply(click::integer::equal_substitute((to_integer(((value + 1) as int32)) - (to_integer((value as int32)) + to_integer((1 as int32)))), 0, ((-1 * (to_integer((value as int32)) + to_integer((1 as int32)))) + to_integer(((value + 1) as int32))), 0)) using {
                        (to_integer(((value + 1) as int32)) - (to_integer((value as int32)) +
                            to_integer((1 as int32)))) == 0;
                        ((-1 * (to_integer((value as int32)) + to_integer((1 as int32)))) +
                            to_integer(((value + 1) as int32))) == (to_integer(((value + 1) as int32)) -
                            (to_integer((value as int32)) + to_integer((1 as int32))));
                        (let integer_value: Integer = 0; integer_value) == 0;
                        defined(((value + 1) as int32));
                        defined((value + 1));
                        defined(old(((value + 1) as int32)));
                        defined(old((value + 1)));
                    };
                }
                have (to_integer((value as int32)) + to_integer((1 as int32)) + (-1 * to_integer(((value + 1) as int32)))) <= 0 by {
                    have (((-1 * (to_integer((value as int32)) + to_integer((1 as int32)))) + to_integer(((value + 1) as int32))) * -1) == (0 * -1) by {
                        apply(click::integer::equal_multiply(((-1 * (to_integer((value as int32)) + to_integer((1 as int32)))) + to_integer(((value + 1) as int32))), 0, -1)) using {
                            ((-1 * (to_integer((value as int32)) + to_integer((1 as int32)))) +
                                to_integer(((value + 1) as int32))) == 0;
                            defined(((value + 1) as int32));
                            defined((value + 1));
                            defined(old(((value + 1) as int32)));
                            defined(old((value + 1)));
                        };
                    }
                    have (to_integer((value as int32)) + to_integer((1 as int32)) + (-1 * to_integer(((value + 1) as int32)))) == 0 by {
                        have (to_integer((value as int32)) + to_integer((1 as int32)) + (-1 * to_integer(((value + 1) as int32)))) == (((-1 * (to_integer((value as int32)) + to_integer((1 as int32)))) + to_integer(((value + 1) as int32))) * -1) by {
                            normalize();
                        }
                        have (let integer_value: Integer = 0; integer_value) == (0 * -1) by {
                            normalize();
                        }
                        apply(click::integer::equal_substitute((((-1 * (to_integer((value as int32)) + to_integer((1 as int32)))) + to_integer(((value + 1) as int32))) * -1), (0 * -1), (to_integer((value as int32)) + to_integer((1 as int32)) + (-1 * to_integer(((value + 1) as int32)))), 0)) using {
                            (((-1 * (to_integer((value as int32)) + to_integer((1 as int32)))) +
                                to_integer(((value + 1) as int32))) * -1) == (0 * -1);
                            (to_integer((value as int32)) + to_integer((1 as int32)) + (-1 *
                                to_integer(((value + 1) as int32)))) == (((-1 * (to_integer((value as
                                int32)) + to_integer((1 as int32)))) + to_integer(((value + 1) as
                                int32))) * -1);
                            (let integer_value: Integer = 0; integer_value) == (0 * -1);
                            defined(((value + 1) as int32));
                            defined((value + 1));
                            defined(old(((value + 1) as int32)));
                            defined(old((value + 1)));
                        };
                    }
                    apply(click::integer::equal_le((to_integer((value as int32)) + to_integer((1 as int32)) + (-1 * to_integer(((value + 1) as int32)))), 0)) using {
                        (to_integer((value as int32)) + to_integer((1 as int32)) + (-1 *
                            to_integer(((value + 1) as int32)))) == 0;
                        defined(((value + 1) as int32));
                        defined((value + 1));
                        defined(old(((value + 1) as int32)));
                        defined(old((value + 1)));
                    };
                }
                have (to_integer((value as int32)) + to_integer((1 as int32)) + (-1 * to_integer(((value + 1) as int32)))) == ((to_integer(((value as int32) as int32)) + 1) - to_integer((((value + 1) as int32) as int32))) by {
                    normalize();
                }
                apply(click::integer::difference_le((to_integer(((value as int32) as int32)) + 1), to_integer((((value + 1) as int32) as int32)), (to_integer((value as int32)) + to_integer((1 as int32)) + (-1 * to_integer(((value + 1) as int32)))))) using {
                    (to_integer((value as int32)) + to_integer((1 as int32)) + (-1 * to_integer(((value
                        + 1) as int32)))) <= 0;
                    (to_integer((value as int32)) + to_integer((1 as int32)) + (-1 * to_integer(((value
                        + 1) as int32)))) == ((to_integer(((value as int32) as int32)) + 1) -
                        to_integer((((value + 1) as int32) as int32)));
                    defined(((value + 1) as int32));
                    defined((value + 1));
                    defined(old(((value + 1) as int32)));
                    defined(old((value + 1)));
                };
                apply(click::integer::step_le_lt(to_integer(((value as int32) as int32)), to_integer((((value + 1) as int32) as int32)))) using {
                    (to_integer(((value as int32) as int32)) + 1) <= to_integer((((value + 1) as int32)
                        as int32));
                    defined(((value + 1) as int32));
                    defined((value + 1));
                    defined(old(((value + 1) as int32)));
                    defined(old((value + 1)));
                };
            }
            normalize() using {
                to_integer(((value as int32) as int32)) < to_integer((((value + 1) as int32) as int32));
            };
        }
        have to_integer(value) < to_integer((value + 1)) by {
            normalize() using {
                (value as int32) < ((value + 1) as int32);
                to_integer(((value + 1) as int32)) == (to_integer((value as int32)) + to_integer((1 as
                    int32)));
            };
        }
        known();
    }
}

theorem int32_increment_lower_bound(value: int32, lower: int32, upper: int32) {
    requires lower <= value;
    requires value < upper;

    ensures to_integer(lower) <= to_integer(value + 1) by {
        have to_integer((-2147483648 as int32)) <= to_integer((lower as int32)) by {
            normalize() using {};
        }
        have (to_integer(((lower as int32) as int32)) + to_integer((-2147483648 as int32))) <= (to_integer(((value as int32) as int32)) + to_integer((lower as int32))) by {
            have (to_integer(((lower as int32) as int32)) + to_integer((-2147483648 as int32))) <= (to_integer(((value as int32) as int32)) + to_integer((lower as int32))) by {
                have ((-1 * to_integer((((value as int32) as int32) as int32))) + to_integer((((lower as int32) as int32) as int32))) <= 0 by {
                    have to_integer((((lower as int32) as int32) as int32)) <= to_integer((((value as int32) as int32) as int32)) by {
                        normalize() using {
                            ((lower as int32) as int32) <= ((value as int32) as int32);
                        };
                    }
                    have ((-1 * to_integer((((value as int32) as int32) as int32))) + to_integer((((lower as int32) as int32) as int32))) == (to_integer((((lower as int32) as int32) as int32)) - to_integer((((value as int32) as int32) as int32))) by {
                        normalize();
                    }
                    apply(click::integer::le_difference(to_integer((((lower as int32) as int32) as int32)), to_integer((((value as int32) as int32) as int32)), ((-1 * to_integer((((value as int32) as int32) as int32))) + to_integer((((lower as int32) as int32) as int32))))) using {
                        to_integer((((lower as int32) as int32) as int32)) <= to_integer((((value as
                            int32) as int32) as int32));
                        ((-1 * to_integer((((value as int32) as int32) as int32))) + to_integer((((lower
                            as int32) as int32) as int32))) == (to_integer((((lower as int32) as int32)
                            as int32)) - to_integer((((value as int32) as int32) as int32)));
                    };
                }
                have ((-1 * to_integer((((lower as int32) as int32) as int32))) + -to_integer(2147483648u64)) <= 0 by {
                    have ((-1 * to_integer((((lower as int32) as int32) as int32))) + -to_integer(2147483648u64)) == (to_integer((-2147483648 as int32)) - to_integer((lower as int32))) by {
                        normalize();
                    }
                    apply(click::integer::le_difference(to_integer((-2147483648 as int32)), to_integer((lower as int32)), ((-1 * to_integer((((lower as int32) as int32) as int32))) + -to_integer(2147483648u64)))) using {
                        to_integer((-2147483648 as int32)) <= to_integer((lower as int32));
                        ((-1 * to_integer((((lower as int32) as int32) as int32))) +
                            -to_integer(2147483648u64)) == (to_integer((-2147483648 as int32)) -
                            to_integer((lower as int32)));
                    };
                }
                have ((-1 * to_integer((((value as int32) as int32) as int32))) + -to_integer(2147483648u64)) <= 0 by {
                    have ((-1 * to_integer((((value as int32) as int32) as int32))) + to_integer((((lower as int32) as int32) as int32)) + ((-1 * to_integer((((lower as int32) as int32) as int32))) + -to_integer(2147483648u64))) <= (0 + 0) by {
                        apply(click::integer::add_le(((-1 * to_integer((((value as int32) as int32) as int32))) + to_integer((((lower as int32) as int32) as int32))), 0, ((-1 * to_integer((((lower as int32) as int32) as int32))) + -to_integer(2147483648u64)), 0)) using {
                            ((-1 * to_integer((((value as int32) as int32) as int32))) +
                                to_integer((((lower as int32) as int32) as int32))) <= 0;
                            ((-1 * to_integer((((lower as int32) as int32) as int32))) +
                                -to_integer(2147483648u64)) <= 0;
                        };
                    }
                    have ((-1 * to_integer((((value as int32) as int32) as int32))) + -to_integer(2147483648u64)) == ((-1 * to_integer((((value as int32) as int32) as int32))) + to_integer((((lower as int32) as int32) as int32)) + ((-1 * to_integer((((lower as int32) as int32) as int32))) + -to_integer(2147483648u64))) by {
                        normalize();
                    }
                    have (let integer_value: Integer = 0; integer_value) == (0 + 0) by {
                        normalize();
                    }
                    apply(click::integer::le_substitute(((-1 * to_integer((((value as int32) as int32) as int32))) + to_integer((((lower as int32) as int32) as int32)) + ((-1 * to_integer((((lower as int32) as int32) as int32))) + -to_integer(2147483648u64))), (0 + 0), ((-1 * to_integer((((value as int32) as int32) as int32))) + -to_integer(2147483648u64)), 0)) using {
                        ((-1 * to_integer((((value as int32) as int32) as int32))) + to_integer((((lower
                            as int32) as int32) as int32)) + ((-1 * to_integer((((lower as int32) as
                            int32) as int32))) + -to_integer(2147483648u64))) <= (0 + 0);
                        ((-1 * to_integer((((value as int32) as int32) as int32))) +
                            -to_integer(2147483648u64)) == ((-1 * to_integer((((value as int32) as
                            int32) as int32))) + to_integer((((lower as int32) as int32) as int32)) +
                            ((-1 * to_integer((((lower as int32) as int32) as int32))) +
                            -to_integer(2147483648u64)));
                        (let integer_value: Integer = 0; integer_value) == (0 + 0);
                    };
                }
                have ((-1 * to_integer((((value as int32) as int32) as int32))) + -to_integer(2147483648u64)) == ((to_integer(((lower as int32) as int32)) + to_integer((-2147483648 as int32))) - (to_integer(((value as int32) as int32)) + to_integer((lower as int32)))) by {
                    normalize();
                }
                apply(click::integer::difference_le((to_integer(((lower as int32) as int32)) + to_integer((-2147483648 as int32))), (to_integer(((value as int32) as int32)) + to_integer((lower as int32))), ((-1 * to_integer((((value as int32) as int32) as int32))) + -to_integer(2147483648u64)))) using {
                    ((-1 * to_integer((((value as int32) as int32) as int32))) +
                        -to_integer(2147483648u64)) <= 0;
                    ((-1 * to_integer((((value as int32) as int32) as int32))) +
                        -to_integer(2147483648u64)) == ((to_integer(((lower as int32) as int32)) +
                        to_integer((-2147483648 as int32))) - (to_integer(((value as int32) as int32)) +
                        to_integer((lower as int32))));
                };
            }
            normalize() using {
                (to_integer(((lower as int32) as int32)) + to_integer((-2147483648 as int32))) <=
                    (to_integer(((value as int32) as int32)) + to_integer((lower as int32)));
            };
        }
        have to_integer((upper as int32)) <= to_integer((2147483647 as int32)) by {
            normalize() using {};
        }
        have (to_integer(((value as int32) as int32)) + to_integer((upper as int32))) < (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32))) by {
            have (to_integer(((value as int32) as int32)) + to_integer((upper as int32))) < (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32))) by {
                have (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((upper as int32) as int32) as int32))) + 1) <= 0 by {
                    have to_integer((((value as int32) as int32) as int32)) < to_integer((((upper as int32) as int32) as int32)) by {
                        normalize() using {
                            ((value as int32) as int32) < ((upper as int32) as int32);
                        };
                    }
                    have (to_integer((((value as int32) as int32) as int32)) + 1) <= to_integer((((upper as int32) as int32) as int32)) by {
                        apply(click::integer::lt_step_le(to_integer((((value as int32) as int32) as int32)), to_integer((((upper as int32) as int32) as int32)))) using {
                            to_integer((((value as int32) as int32) as int32)) < to_integer((((upper as
                                int32) as int32) as int32));
                        };
                    }
                    have (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((upper as int32) as int32) as int32))) + 1) == ((to_integer((((value as int32) as int32) as int32)) + 1) - to_integer((((upper as int32) as int32) as int32))) by {
                        normalize();
                    }
                    apply(click::integer::le_difference((to_integer((((value as int32) as int32) as int32)) + 1), to_integer((((upper as int32) as int32) as int32)), (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((upper as int32) as int32) as int32))) + 1))) using {
                        (to_integer((((value as int32) as int32) as int32)) + 1) <= to_integer((((upper
                            as int32) as int32) as int32));
                        (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((upper
                            as int32) as int32) as int32))) + 1) == ((to_integer((((value as int32) as
                            int32) as int32)) + 1) - to_integer((((upper as int32) as int32) as
                            int32)));
                    };
                }
                have (to_integer((((upper as int32) as int32) as int32)) + -2147483647) <= 0 by {
                    have (to_integer((((upper as int32) as int32) as int32)) + -2147483647) == (to_integer((upper as int32)) - to_integer((2147483647 as int32))) by {
                        normalize();
                    }
                    apply(click::integer::le_difference(to_integer((upper as int32)), to_integer((2147483647 as int32)), (to_integer((((upper as int32) as int32) as int32)) + -2147483647))) using {
                        to_integer((upper as int32)) <= to_integer((2147483647 as int32));
                        (to_integer((((upper as int32) as int32) as int32)) + -2147483647) ==
                            (to_integer((upper as int32)) - to_integer((2147483647 as int32)));
                    };
                }
                have (to_integer((((value as int32) as int32) as int32)) + -2147483646) <= 0 by {
                    have (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((upper as int32) as int32) as int32))) + 1 + (to_integer((((upper as int32) as int32) as int32)) + -2147483647)) <= (0 + 0) by {
                        apply(click::integer::add_le((to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((upper as int32) as int32) as int32))) + 1), 0, (to_integer((((upper as int32) as int32) as int32)) + -2147483647), 0)) using {
                            (to_integer((((value as int32) as int32) as int32)) + (-1 *
                                to_integer((((upper as int32) as int32) as int32))) + 1) <= 0;
                            (to_integer((((upper as int32) as int32) as int32)) + -2147483647) <= 0;
                        };
                    }
                    have (to_integer((((value as int32) as int32) as int32)) + -2147483646) == (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((upper as int32) as int32) as int32))) + 1 + (to_integer((((upper as int32) as int32) as int32)) + -2147483647)) by {
                        normalize();
                    }
                    have (let integer_value: Integer = 0; integer_value) == (0 + 0) by {
                        normalize();
                    }
                    apply(click::integer::le_substitute((to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((upper as int32) as int32) as int32))) + 1 + (to_integer((((upper as int32) as int32) as int32)) + -2147483647)), (0 + 0), (to_integer((((value as int32) as int32) as int32)) + -2147483646), 0)) using {
                        (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((upper
                            as int32) as int32) as int32))) + 1 + (to_integer((((upper as int32) as
                            int32) as int32)) + -2147483647)) <= (0 + 0);
                        (to_integer((((value as int32) as int32) as int32)) + -2147483646) ==
                            (to_integer((((value as int32) as int32) as int32)) + (-1 *
                            to_integer((((upper as int32) as int32) as int32))) + 1 +
                            (to_integer((((upper as int32) as int32) as int32)) + -2147483647));
                        (let integer_value: Integer = 0; integer_value) == (0 + 0);
                    };
                }
                have (to_integer((((value as int32) as int32) as int32)) + -2147483646) == ((to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + 1) - (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32)))) by {
                    normalize();
                }
                apply(click::integer::difference_le((to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + 1), (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32))), (to_integer((((value as int32) as int32) as int32)) + -2147483646))) using {
                    (to_integer((((value as int32) as int32) as int32)) + -2147483646) <= 0;
                    (to_integer((((value as int32) as int32) as int32)) + -2147483646) ==
                        ((to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + 1) -
                        (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32))));
                };
                apply(click::integer::step_le_lt((to_integer(((value as int32) as int32)) + to_integer((upper as int32))), (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32))))) using {
                    (to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + 1) <=
                        (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32)));
                };
            }
            normalize() using {
                (to_integer(((value as int32) as int32)) + to_integer((upper as int32))) <
                    (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32)));
            };
        }
        have -2147483648 <= to_integer((value as int32)) by {
            normalize() using {
                (to_integer(((lower as int32) as int32)) + to_integer((-2147483648 as int32))) <=
                    (to_integer(((value as int32) as int32)) + to_integer((lower as int32)));
            };
        }
        have to_integer((value as int32)) <= 2147483647 by {
            normalize() using {
                (to_integer(((lower as int32) as int32)) + to_integer((-2147483648 as int32))) <=
                    (to_integer(((value as int32) as int32)) + to_integer((lower as int32)));
            };
        }
        have -2147483648 <= to_integer((value as int32)) by {
            normalize() using {
                (to_integer(((value as int32) as int32)) + to_integer((upper as int32))) <
                    (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32)));
            };
        }
        have to_integer((value as int32)) <= 2147483646 by {
            have to_integer((value as int32)) <= 2147483646 by {
                have (to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + (-1 * (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32)))) + 1) <= 0 by {
                    have (to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + 1) <= (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32))) by {
                        apply(click::integer::lt_step_le((to_integer(((value as int32) as int32)) + to_integer((upper as int32))), (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32))))) using {
                            (to_integer(((value as int32) as int32)) + to_integer((upper as int32))) <
                                (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as
                                int32)));
                        };
                    }
                    have (to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + (-1 * (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32)))) + 1) == ((to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + 1) - (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32)))) by {
                        normalize();
                    }
                    apply(click::integer::le_difference((to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + 1), (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32))), (to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + (-1 * (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32)))) + 1))) using {
                        (to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + 1) <=
                            (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as
                            int32)));
                        (to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + (-1 *
                            (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as
                            int32)))) + 1) == ((to_integer(((value as int32) as int32)) +
                            to_integer((upper as int32)) + 1) - (to_integer(((upper as int32) as int32))
                            + to_integer((2147483647 as int32))));
                    };
                }
                have (to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + (-1 * (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32)))) + 1) == (to_integer((value as int32)) - 2147483646) by {
                    normalize();
                }
                apply(click::integer::difference_le(to_integer((value as int32)), 2147483646, (to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + (-1 * (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32)))) + 1))) using {
                    (to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + (-1 *
                        (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32)))) +
                        1) <= 0;
                    (to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + (-1 *
                        (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32)))) +
                        1) == (to_integer((value as int32)) - 2147483646);
                };
            }
            normalize() using {
                to_integer((value as int32)) <= 2147483646;
            };
        }
        have -2147483648 <= to_integer((value as int32)) by {
            normalize() using {
                -2147483648 <= to_integer((value as int32));
                to_integer((value as int32)) <= 2147483647;
                -2147483648 <= to_integer((value as int32));
                to_integer((value as int32)) <= 2147483646;
            };
        }
        have to_integer((value as int32)) <= 2147483646 by {
            normalize() using {
                -2147483648 <= to_integer((value as int32));
                to_integer((value as int32)) <= 2147483647;
                -2147483648 <= to_integer((value as int32));
                to_integer((value as int32)) <= 2147483646;
            };
        }
        have 1 <= to_integer((1 as int32)) by {
            normalize() using {};
        }
        have to_integer((1 as int32)) <= 1 by {
            normalize() using {};
        }
        have -2147483648 <= (to_integer((value as int32)) + to_integer((1 as int32))) by {
            have -2147483648 <= (to_integer((value as int32)) + to_integer((1 as int32))) by {
                have ((-1 * to_integer((value as int32))) + -to_integer(2147483648u64)) <= 0 by {
                    have ((-1 * to_integer((value as int32))) + -to_integer(2147483648u64)) == (-2147483648 - to_integer((value as int32))) by {
                        normalize();
                    }
                    apply(click::integer::le_difference(-2147483648, to_integer((value as int32)), ((-1 * to_integer((value as int32))) + -to_integer(2147483648u64)))) using {
                        -2147483648 <= to_integer((value as int32));
                        ((-1 * to_integer((value as int32))) + -to_integer(2147483648u64)) ==
                            (-2147483648 - to_integer((value as int32)));
                    };
                }
                have (let integer_constant: Integer = -1; integer_constant) <= 0 by {
                    normalize();
                }
                have ((-1 * to_integer((value as int32))) + -to_integer(2147483649u64)) <= 0 by {
                    have ((-1 * to_integer((value as int32))) + -to_integer(2147483648u64) + (let integer_constant: Integer = -1; integer_constant)) <= (0 + 0) by {
                        apply(click::integer::add_le(((-1 * to_integer((value as int32))) + -to_integer(2147483648u64)), 0, (let integer_constant: Integer = -1; integer_constant), 0)) using {
                            ((-1 * to_integer((value as int32))) + -to_integer(2147483648u64)) <= 0;
                            (let integer_constant: Integer = -1; integer_constant) <= 0;
                        };
                    }
                    have ((-1 * to_integer((value as int32))) + -to_integer(2147483649u64)) == ((-1 * to_integer((value as int32))) + -to_integer(2147483648u64) + (let integer_constant: Integer = -1; integer_constant)) by {
                        normalize();
                    }
                    have (let integer_value: Integer = 0; integer_value) == (0 + 0) by {
                        normalize();
                    }
                    apply(click::integer::le_substitute(((-1 * to_integer((value as int32))) + -to_integer(2147483648u64) + (let integer_constant: Integer = -1; integer_constant)), (0 + 0), ((-1 * to_integer((value as int32))) + -to_integer(2147483649u64)), 0)) using {
                        ((-1 * to_integer((value as int32))) + -to_integer(2147483648u64) + (let
                            integer_constant: Integer = -1; integer_constant)) <= (0 + 0);
                        ((-1 * to_integer((value as int32))) + -to_integer(2147483649u64)) == ((-1 *
                            to_integer((value as int32))) + -to_integer(2147483648u64) + (let
                            integer_constant: Integer = -1; integer_constant));
                        (let integer_value: Integer = 0; integer_value) == (0 + 0);
                    };
                }
                have ((-1 * to_integer((value as int32))) + -to_integer(2147483649u64)) == (-2147483648 - (to_integer((value as int32)) + to_integer((1 as int32)))) by {
                    normalize();
                }
                apply(click::integer::difference_le(-2147483648, (to_integer((value as int32)) + to_integer((1 as int32))), ((-1 * to_integer((value as int32))) + -to_integer(2147483649u64)))) using {
                    ((-1 * to_integer((value as int32))) + -to_integer(2147483649u64)) <= 0;
                    ((-1 * to_integer((value as int32))) + -to_integer(2147483649u64)) == (-2147483648 -
                        (to_integer((value as int32)) + to_integer((1 as int32))));
                };
            }
            normalize() using {
                -2147483648 <= (to_integer((value as int32)) + to_integer((1 as int32)));
            };
        }
        have (to_integer((value as int32)) + to_integer((1 as int32))) <= 2147483647 by {
            have (to_integer((value as int32)) + to_integer((1 as int32))) <= 2147483647 by {
                have (to_integer((value as int32)) + -2147483646) <= 0 by {
                    have (to_integer((value as int32)) + -2147483646) == (to_integer((value as int32)) - 2147483646) by {
                        normalize();
                    }
                    apply(click::integer::le_difference(to_integer((value as int32)), 2147483646, (to_integer((value as int32)) + -2147483646))) using {
                        to_integer((value as int32)) <= 2147483646;
                        (to_integer((value as int32)) + -2147483646) == (to_integer((value as int32)) -
                            2147483646);
                    };
                }
                have (to_integer((value as int32)) + -2147483646) == ((to_integer((value as int32)) + to_integer((1 as int32))) - 2147483647) by {
                    normalize();
                }
                apply(click::integer::difference_le((to_integer((value as int32)) + to_integer((1 as int32))), 2147483647, (to_integer((value as int32)) + -2147483646))) using {
                    (to_integer((value as int32)) + -2147483646) <= 0;
                    (to_integer((value as int32)) + -2147483646) == ((to_integer((value as int32)) +
                        to_integer((1 as int32))) - 2147483647);
                };
            }
            normalize() using {
                (to_integer((value as int32)) + to_integer((1 as int32))) <= 2147483647;
            };
        }
        have defined((value + 1)) by {
            known();
        }
        have to_integer(((value + 1) as int32)) == (to_integer((value as int32)) + to_integer((1 as int32))) by {
            normalize() using {
                -2147483648 <= (to_integer((value as int32)) + to_integer((1 as int32)));
                (to_integer((value as int32)) + to_integer((1 as int32))) <= 2147483647;
            };
        }
        have -2147483647 <= to_integer(((value + 1) as int32)) by {
            normalize() using {
                -2147483648 <= to_integer((value as int32));
                to_integer((value as int32)) <= 2147483646;
                1 <= to_integer((1 as int32));
                to_integer((1 as int32)) <= 1;
                to_integer(((value + 1) as int32)) == (to_integer((value as int32)) + to_integer((1 as
                    int32)));
            };
        }
        have to_integer(((value + 1) as int32)) <= 2147483647 by {
            normalize() using {
                -2147483648 <= to_integer((value as int32));
                to_integer((value as int32)) <= 2147483646;
                1 <= to_integer((1 as int32));
                to_integer((1 as int32)) <= 1;
                to_integer(((value + 1) as int32)) == (to_integer((value as int32)) + to_integer((1 as
                    int32)));
            };
        }
        have -1 <= 0 by {
            normalize() using {
                to_integer(((value + 1) as int32)) == (to_integer((value as int32)) + to_integer((1 as
                    int32)));
            };
        }
        have (to_integer(((lower as int32) as int32)) + -1) <= (to_integer(((value as int32) as int32)) + 0) by {
            have defined(((value + 1) as int32)) by {
                known();
            }
            have defined((value + 1)) by {
                known();
            }
            have defined(old(((value + 1) as int32))) by {
                known();
            }
            have defined(old((value + 1))) by {
                known();
            }
            have (to_integer(((lower as int32) as int32)) + -1) <= (to_integer(((value as int32) as int32)) + 0) by {
                have ((-1 * to_integer((((value as int32) as int32) as int32))) + to_integer((((lower as int32) as int32) as int32))) <= 0 by {
                    have to_integer((((lower as int32) as int32) as int32)) <= to_integer((((value as int32) as int32) as int32)) by {
                        normalize() using {
                            ((lower as int32) as int32) <= ((value as int32) as int32);
                        };
                    }
                    have ((-1 * to_integer((((value as int32) as int32) as int32))) + to_integer((((lower as int32) as int32) as int32))) == (to_integer((((lower as int32) as int32) as int32)) - to_integer((((value as int32) as int32) as int32))) by {
                        normalize();
                    }
                    apply(click::integer::le_difference(to_integer((((lower as int32) as int32) as int32)), to_integer((((value as int32) as int32) as int32)), ((-1 * to_integer((((value as int32) as int32) as int32))) + to_integer((((lower as int32) as int32) as int32))))) using {
                        to_integer((((lower as int32) as int32) as int32)) <= to_integer((((value as
                            int32) as int32) as int32));
                        ((-1 * to_integer((((value as int32) as int32) as int32))) + to_integer((((lower
                            as int32) as int32) as int32))) == (to_integer((((lower as int32) as int32)
                            as int32)) - to_integer((((value as int32) as int32) as int32)));
                        defined(((value + 1) as int32));
                        defined((value + 1));
                        defined(old(((value + 1) as int32)));
                        defined(old((value + 1)));
                    };
                }
                have (let integer_constant: Integer = -1; integer_constant) <= 0 by {
                    normalize();
                }
                have ((-1 * to_integer((((value as int32) as int32) as int32))) + to_integer((((lower as int32) as int32) as int32)) + -1) <= 0 by {
                    have ((-1 * to_integer((((value as int32) as int32) as int32))) + to_integer((((lower as int32) as int32) as int32)) + (let integer_constant: Integer = -1; integer_constant)) <= (0 + 0) by {
                        apply(click::integer::add_le(((-1 * to_integer((((value as int32) as int32) as int32))) + to_integer((((lower as int32) as int32) as int32))), 0, (let integer_constant: Integer = -1; integer_constant), 0)) using {
                            ((-1 * to_integer((((value as int32) as int32) as int32))) +
                                to_integer((((lower as int32) as int32) as int32))) <= 0;
                            (let integer_constant: Integer = -1; integer_constant) <= 0;
                            defined(((value + 1) as int32));
                            defined((value + 1));
                            defined(old(((value + 1) as int32)));
                            defined(old((value + 1)));
                        };
                    }
                    have ((-1 * to_integer((((value as int32) as int32) as int32))) + to_integer((((lower as int32) as int32) as int32)) + -1) == ((-1 * to_integer((((value as int32) as int32) as int32))) + to_integer((((lower as int32) as int32) as int32)) + (let integer_constant: Integer = -1; integer_constant)) by {
                        normalize();
                    }
                    have (let integer_value: Integer = 0; integer_value) == (0 + 0) by {
                        normalize();
                    }
                    apply(click::integer::le_substitute(((-1 * to_integer((((value as int32) as int32) as int32))) + to_integer((((lower as int32) as int32) as int32)) + (let integer_constant: Integer = -1; integer_constant)), (0 + 0), ((-1 * to_integer((((value as int32) as int32) as int32))) + to_integer((((lower as int32) as int32) as int32)) + -1), 0)) using {
                        ((-1 * to_integer((((value as int32) as int32) as int32))) + to_integer((((lower
                            as int32) as int32) as int32)) + (let integer_constant: Integer = -1;
                            integer_constant)) <= (0 + 0);
                        ((-1 * to_integer((((value as int32) as int32) as int32))) + to_integer((((lower
                            as int32) as int32) as int32)) + -1) == ((-1 * to_integer((((value as int32)
                            as int32) as int32))) + to_integer((((lower as int32) as int32) as int32)) +
                            (let integer_constant: Integer = -1; integer_constant));
                        (let integer_value: Integer = 0; integer_value) == (0 + 0);
                        defined(((value + 1) as int32));
                        defined((value + 1));
                        defined(old(((value + 1) as int32)));
                        defined(old((value + 1)));
                    };
                }
                have ((-1 * to_integer((((value as int32) as int32) as int32))) + to_integer((((lower as int32) as int32) as int32)) + -1) == ((to_integer(((lower as int32) as int32)) + -1) - (to_integer(((value as int32) as int32)) + 0)) by {
                    normalize();
                }
                apply(click::integer::difference_le((to_integer(((lower as int32) as int32)) + -1), (to_integer(((value as int32) as int32)) + 0), ((-1 * to_integer((((value as int32) as int32) as int32))) + to_integer((((lower as int32) as int32) as int32)) + -1))) using {
                    ((-1 * to_integer((((value as int32) as int32) as int32))) + to_integer((((lower as
                        int32) as int32) as int32)) + -1) <= 0;
                    ((-1 * to_integer((((value as int32) as int32) as int32))) + to_integer((((lower as
                        int32) as int32) as int32)) + -1) == ((to_integer(((lower as int32) as int32)) +
                        -1) - (to_integer(((value as int32) as int32)) + 0));
                    defined(((value + 1) as int32));
                    defined((value + 1));
                    defined(old(((value + 1) as int32)));
                    defined(old((value + 1)));
                };
            }
            normalize() using {
                (to_integer(((lower as int32) as int32)) + -1) <= (to_integer(((value as int32) as
                    int32)) + 0);
            };
        }
        have (lower as int32) <= ((value + 1) as int32) by {
            have defined(((value + 1) as int32)) by {
                known();
            }
            have defined((value + 1)) by {
                known();
            }
            have defined(old(((value + 1) as int32))) by {
                known();
            }
            have defined(old((value + 1))) by {
                known();
            }
            have to_integer(((lower as int32) as int32)) <= to_integer((((value + 1) as int32) as int32)) by {
                have (to_integer(((lower as int32) as int32)) + -1 + (-1 * (to_integer(((value as int32) as int32)) + 0))) <= 0 by {
                    have (to_integer(((lower as int32) as int32)) + -1 + (-1 * (to_integer(((value as int32) as int32)) + 0))) == ((to_integer(((lower as int32) as int32)) + -1) - (to_integer(((value as int32) as int32)) + 0)) by {
                        normalize();
                    }
                    apply(click::integer::le_difference((to_integer(((lower as int32) as int32)) + -1), (to_integer(((value as int32) as int32)) + 0), (to_integer(((lower as int32) as int32)) + -1 + (-1 * (to_integer(((value as int32) as int32)) + 0))))) using {
                        (to_integer(((lower as int32) as int32)) + -1) <= (to_integer(((value as int32)
                            as int32)) + 0);
                        (to_integer(((lower as int32) as int32)) + -1 + (-1 * (to_integer(((value as
                            int32) as int32)) + 0))) == ((to_integer(((lower as int32) as int32)) + -1)
                            - (to_integer(((value as int32) as int32)) + 0));
                        defined(((value + 1) as int32));
                        defined((value + 1));
                        defined(old(((value + 1) as int32)));
                        defined(old((value + 1)));
                    };
                }
                have ((-1 * (to_integer((value as int32)) + to_integer((1 as int32)))) + to_integer(((value + 1) as int32))) == 0 by {
                    have (to_integer(((value + 1) as int32)) - (to_integer((value as int32)) + to_integer((1 as int32)))) == 0 by {
                        apply(click::integer::equal_difference(to_integer(((value + 1) as int32)), (to_integer((value as int32)) + to_integer((1 as int32))))) using {
                            to_integer(((value + 1) as int32)) == (to_integer((value as int32)) +
                                to_integer((1 as int32)));
                            defined(((value + 1) as int32));
                            defined((value + 1));
                            defined(old(((value + 1) as int32)));
                            defined(old((value + 1)));
                        };
                    }
                    have ((-1 * (to_integer((value as int32)) + to_integer((1 as int32)))) + to_integer(((value + 1) as int32))) == (to_integer(((value + 1) as int32)) - (to_integer((value as int32)) + to_integer((1 as int32)))) by {
                        normalize();
                    }
                    apply(click::integer::equal_substitute((to_integer(((value + 1) as int32)) - (to_integer((value as int32)) + to_integer((1 as int32)))), 0, ((-1 * (to_integer((value as int32)) + to_integer((1 as int32)))) + to_integer(((value + 1) as int32))), 0)) using {
                        (to_integer(((value + 1) as int32)) - (to_integer((value as int32)) +
                            to_integer((1 as int32)))) == 0;
                        ((-1 * (to_integer((value as int32)) + to_integer((1 as int32)))) +
                            to_integer(((value + 1) as int32))) == (to_integer(((value + 1) as int32)) -
                            (to_integer((value as int32)) + to_integer((1 as int32))));
                        (let integer_value: Integer = 0; integer_value) == 0;
                        defined(((value + 1) as int32));
                        defined((value + 1));
                        defined(old(((value + 1) as int32)));
                        defined(old((value + 1)));
                    };
                }
                have (to_integer((value as int32)) + to_integer((1 as int32)) + (-1 * to_integer(((value + 1) as int32)))) <= 0 by {
                    have (((-1 * (to_integer((value as int32)) + to_integer((1 as int32)))) + to_integer(((value + 1) as int32))) * -1) == (0 * -1) by {
                        apply(click::integer::equal_multiply(((-1 * (to_integer((value as int32)) + to_integer((1 as int32)))) + to_integer(((value + 1) as int32))), 0, -1)) using {
                            ((-1 * (to_integer((value as int32)) + to_integer((1 as int32)))) +
                                to_integer(((value + 1) as int32))) == 0;
                            defined(((value + 1) as int32));
                            defined((value + 1));
                            defined(old(((value + 1) as int32)));
                            defined(old((value + 1)));
                        };
                    }
                    have (to_integer((value as int32)) + to_integer((1 as int32)) + (-1 * to_integer(((value + 1) as int32)))) == 0 by {
                        have (to_integer((value as int32)) + to_integer((1 as int32)) + (-1 * to_integer(((value + 1) as int32)))) == (((-1 * (to_integer((value as int32)) + to_integer((1 as int32)))) + to_integer(((value + 1) as int32))) * -1) by {
                            normalize();
                        }
                        have (let integer_value: Integer = 0; integer_value) == (0 * -1) by {
                            normalize();
                        }
                        apply(click::integer::equal_substitute((((-1 * (to_integer((value as int32)) + to_integer((1 as int32)))) + to_integer(((value + 1) as int32))) * -1), (0 * -1), (to_integer((value as int32)) + to_integer((1 as int32)) + (-1 * to_integer(((value + 1) as int32)))), 0)) using {
                            (((-1 * (to_integer((value as int32)) + to_integer((1 as int32)))) +
                                to_integer(((value + 1) as int32))) * -1) == (0 * -1);
                            (to_integer((value as int32)) + to_integer((1 as int32)) + (-1 *
                                to_integer(((value + 1) as int32)))) == (((-1 * (to_integer((value as
                                int32)) + to_integer((1 as int32)))) + to_integer(((value + 1) as
                                int32))) * -1);
                            (let integer_value: Integer = 0; integer_value) == (0 * -1);
                            defined(((value + 1) as int32));
                            defined((value + 1));
                            defined(old(((value + 1) as int32)));
                            defined(old((value + 1)));
                        };
                    }
                    apply(click::integer::equal_le((to_integer((value as int32)) + to_integer((1 as int32)) + (-1 * to_integer(((value + 1) as int32)))), 0)) using {
                        (to_integer((value as int32)) + to_integer((1 as int32)) + (-1 *
                            to_integer(((value + 1) as int32)))) == 0;
                        defined(((value + 1) as int32));
                        defined((value + 1));
                        defined(old(((value + 1) as int32)));
                        defined(old((value + 1)));
                    };
                }
                have (to_integer((value as int32)) + to_integer((1 as int32)) + (-1 * to_integer(((value + 1) as int32))) + (to_integer(((lower as int32) as int32)) + -1) + (-1 * (to_integer(((value as int32) as int32)) + 0))) <= 0 by {
                    have (to_integer(((lower as int32) as int32)) + -1 + (-1 * (to_integer(((value as int32) as int32)) + 0)) + (to_integer((value as int32)) + to_integer((1 as int32)) + (-1 * to_integer(((value + 1) as int32))))) <= (0 + 0) by {
                        apply(click::integer::add_le((to_integer(((lower as int32) as int32)) + -1 + (-1 * (to_integer(((value as int32) as int32)) + 0))), 0, (to_integer((value as int32)) + to_integer((1 as int32)) + (-1 * to_integer(((value + 1) as int32)))), 0)) using {
                            (to_integer(((lower as int32) as int32)) + -1 + (-1 * (to_integer(((value as
                                int32) as int32)) + 0))) <= 0;
                            (to_integer((value as int32)) + to_integer((1 as int32)) + (-1 *
                                to_integer(((value + 1) as int32)))) <= 0;
                            defined(((value + 1) as int32));
                            defined((value + 1));
                            defined(old(((value + 1) as int32)));
                            defined(old((value + 1)));
                        };
                    }
                    have (to_integer((value as int32)) + to_integer((1 as int32)) + (-1 * to_integer(((value + 1) as int32))) + (to_integer(((lower as int32) as int32)) + -1) + (-1 * (to_integer(((value as int32) as int32)) + 0))) == (to_integer(((lower as int32) as int32)) + -1 + (-1 * (to_integer(((value as int32) as int32)) + 0)) + (to_integer((value as int32)) + to_integer((1 as int32)) + (-1 * to_integer(((value + 1) as int32))))) by {
                        normalize();
                    }
                    have (let integer_value: Integer = 0; integer_value) == (0 + 0) by {
                        normalize();
                    }
                    apply(click::integer::le_substitute((to_integer(((lower as int32) as int32)) + -1 + (-1 * (to_integer(((value as int32) as int32)) + 0)) + (to_integer((value as int32)) + to_integer((1 as int32)) + (-1 * to_integer(((value + 1) as int32))))), (0 + 0), (to_integer((value as int32)) + to_integer((1 as int32)) + (-1 * to_integer(((value + 1) as int32))) + (to_integer(((lower as int32) as int32)) + -1) + (-1 * (to_integer(((value as int32) as int32)) + 0))), 0)) using {
                        (to_integer(((lower as int32) as int32)) + -1 + (-1 * (to_integer(((value as
                            int32) as int32)) + 0)) + (to_integer((value as int32)) + to_integer((1 as
                            int32)) + (-1 * to_integer(((value + 1) as int32))))) <= (0 + 0);
                        (to_integer((value as int32)) + to_integer((1 as int32)) + (-1 *
                            to_integer(((value + 1) as int32))) + (to_integer(((lower as int32) as
                            int32)) + -1) + (-1 * (to_integer(((value as int32) as int32)) + 0))) ==
                            (to_integer(((lower as int32) as int32)) + -1 + (-1 * (to_integer(((value as
                            int32) as int32)) + 0)) + (to_integer((value as int32)) + to_integer((1 as
                            int32)) + (-1 * to_integer(((value + 1) as int32)))));
                        (let integer_value: Integer = 0; integer_value) == (0 + 0);
                        defined(((value + 1) as int32));
                        defined((value + 1));
                        defined(old(((value + 1) as int32)));
                        defined(old((value + 1)));
                    };
                }
                have (to_integer((value as int32)) + to_integer((1 as int32)) + (-1 * to_integer(((value + 1) as int32))) + (to_integer(((lower as int32) as int32)) + -1) + (-1 * (to_integer(((value as int32) as int32)) + 0))) == (to_integer(((lower as int32) as int32)) - to_integer((((value + 1) as int32) as int32))) by {
                    normalize();
                }
                apply(click::integer::difference_le(to_integer(((lower as int32) as int32)), to_integer((((value + 1) as int32) as int32)), (to_integer((value as int32)) + to_integer((1 as int32)) + (-1 * to_integer(((value + 1) as int32))) + (to_integer(((lower as int32) as int32)) + -1) + (-1 * (to_integer(((value as int32) as int32)) + 0))))) using {
                    (to_integer((value as int32)) + to_integer((1 as int32)) + (-1 * to_integer(((value
                        + 1) as int32))) + (to_integer(((lower as int32) as int32)) + -1) + (-1 *
                        (to_integer(((value as int32) as int32)) + 0))) <= 0;
                    (to_integer((value as int32)) + to_integer((1 as int32)) + (-1 * to_integer(((value
                        + 1) as int32))) + (to_integer(((lower as int32) as int32)) + -1) + (-1 *
                        (to_integer(((value as int32) as int32)) + 0))) == (to_integer(((lower as int32)
                        as int32)) - to_integer((((value + 1) as int32) as int32)));
                    defined(((value + 1) as int32));
                    defined((value + 1));
                    defined(old(((value + 1) as int32)));
                    defined(old((value + 1)));
                };
            }
            normalize() using {
                to_integer(((lower as int32) as int32)) <= to_integer((((value + 1) as int32) as
                    int32));
            };
        }
        have to_integer(lower) <= to_integer((value + 1)) by {
            normalize() using {
                (lower as int32) <= ((value + 1) as int32);
                to_integer(((value + 1) as int32)) == (to_integer((value as int32)) + to_integer((1 as
                    int32)));
            };
        }
        known();
    }
}

theorem int32_positive_is_nonnegative(value: int32) {
    requires 0 < value;

    ensures 0 <= value by {
        normalize() using { 0 < value; };
    }
}

theorem int32_increment_below_max_is_defined(value: int32) {
    requires value < 2147483647;

    ensures defined(value + 1) by {
        have -2147483648 <= to_integer(value) by normalize();
        have to_integer(value) + 1 <= 2147483647 by {
            apply(integer::lt_step_le(to_integer(value), 2147483647)) using { to_integer(value) < 2147483647; };
        }
        have -2147483648 + 0 <= to_integer(value) + 1 by {
            apply(integer::add_le(-2147483648, to_integer(value), 0, 1)) using { -2147483648 <= to_integer(value); 0 <= 1; };
        }
        have -2147483648 == -2147483648 + 0 by normalize();
        have -2147483648 <= to_integer(value) + 1 by {
            apply(integer::le_substitute(-2147483648 + 0, to_integer(value) + 1, -2147483648, to_integer(value) + 1)) using {
                -2147483648 + 0 <= to_integer(value) + 1;
                -2147483648 == -2147483648 + 0;
                to_integer(value) + 1 == to_integer(value) + 1;
            };
        }
        known();
    }
}

theorem int32_nonnegative_add_within_max_is_defined(value: int32, amount: int32) {
    requires 0 <= amount;
    requires to_integer(value) <= to_integer(2147483647 - amount);

    ensures defined(value + amount) by {
        have -2147483648 <= (2147483647 - to_integer(amount)) by {
            have -2147483648 <= (2147483647 - to_integer(amount)) by {
                have (to_integer(amount) + -2147483647) <= 0 by {
                    have to_integer(amount) <= 2147483647 by {
                        normalize();
                    }
                    have (to_integer(amount) + -2147483647) == (to_integer(amount) - 2147483647) by {
                        normalize();
                    }
                    apply(integer::le_difference(to_integer(amount), 2147483647, (to_integer(amount) + -2147483647))) using {
                        to_integer(amount) <= 2147483647;
                        (to_integer(amount) + -2147483647) == (to_integer(amount) - 2147483647);
                    };
                }
                have (let integer_constant: Integer = -to_integer(2147483648u64); integer_constant) <= 0 by {
                    normalize();
                }
                have (to_integer(amount) + -to_integer(4294967295u64)) <= 0 by {
                    have (to_integer(amount) + -2147483647 + (let integer_constant: Integer = -to_integer(2147483648u64); integer_constant)) <= (0 + 0) by {
                        apply(integer::add_le((to_integer(amount) + -2147483647), 0, (let integer_constant: Integer = -to_integer(2147483648u64); integer_constant), 0)) using {
                            (to_integer(amount) + -2147483647) <= 0;
                            (let integer_constant: Integer = -to_integer(2147483648u64);
                                integer_constant) <= 0;
                        };
                    }
                    have (to_integer(amount) + -to_integer(4294967295u64)) == (to_integer(amount) + -2147483647 + (let integer_constant: Integer = -to_integer(2147483648u64); integer_constant)) by {
                        normalize();
                    }
                    have (let integer_value: Integer = 0; integer_value) == (0 + 0) by {
                        normalize();
                    }
                    apply(integer::le_substitute((to_integer(amount) + -2147483647 + (let integer_constant: Integer = -to_integer(2147483648u64); integer_constant)), (0 + 0), (to_integer(amount) + -to_integer(4294967295u64)), 0)) using {
                        (to_integer(amount) + -2147483647 + (let integer_constant: Integer =
                            -to_integer(2147483648u64); integer_constant)) <= (0 + 0);
                        (to_integer(amount) + -to_integer(4294967295u64)) == (to_integer(amount) +
                            -2147483647 + (let integer_constant: Integer = -to_integer(2147483648u64);
                            integer_constant));
                        (let integer_value: Integer = 0; integer_value) == (0 + 0);
                    };
                }
                have (to_integer(amount) + -to_integer(4294967295u64)) == (-2147483648 - (2147483647 - to_integer(amount))) by {
                    normalize();
                }
                apply(integer::difference_le(-2147483648, (2147483647 - to_integer(amount)), (to_integer(amount) + -to_integer(4294967295u64)))) using {
                    (to_integer(amount) + -to_integer(4294967295u64)) <= 0;
                    (to_integer(amount) + -to_integer(4294967295u64)) == (-2147483648 - (2147483647 -
                        to_integer(amount)));
                };
            }
            normalize() using {
                -2147483648 <= (2147483647 - to_integer(amount));
            };
        }
        have (2147483647 - to_integer(amount)) <= 2147483647 by {
            have (2147483647 - to_integer(amount)) <= 2147483647 by {
                have (-1 * to_integer(amount)) <= 0 by {
                    have (-1 * to_integer(amount)) == (0 - to_integer(amount)) by {
                        normalize();
                    }
                    apply(integer::le_difference(0, to_integer(amount), (-1 * to_integer(amount)))) using {
                        0 <= to_integer(amount);
                        (-1 * to_integer(amount)) == (0 - to_integer(amount));
                    };
                }
                have (-1 * to_integer(amount)) == ((2147483647 - to_integer(amount)) - 2147483647) by {
                    normalize();
                }
                apply(integer::difference_le((2147483647 - to_integer(amount)), 2147483647, (-1 * to_integer(amount)))) using {
                    (-1 * to_integer(amount)) <= 0;
                    (-1 * to_integer(amount)) == ((2147483647 - to_integer(amount)) - 2147483647);
                };
            }
            normalize() using {
                (2147483647 - to_integer(amount)) <= 2147483647;
            };
        }
        have to_integer((2147483647 - amount)) == (2147483647 - to_integer(amount)) by {
            normalize() using {
                -2147483648 <= (2147483647 - to_integer(amount));
                (2147483647 - to_integer(amount)) <= 2147483647;
            };
        }
        have -2147483648 <= (to_integer(value) + to_integer(amount)) by {
            have -2147483648 <= (to_integer(value) + to_integer(amount)) by {
                have (-1 * to_integer(amount)) <= 0 by {
                    have (-1 * to_integer(amount)) == (0 - to_integer(amount)) by {
                        normalize();
                    }
                    apply(integer::le_difference(0, to_integer(amount), (-1 * to_integer(amount)))) using {
                        0 <= to_integer(amount);
                        (-1 * to_integer(amount)) == (0 - to_integer(amount));
                    };
                }
                have ((-1 * to_integer(value)) + -to_integer(2147483648u64)) <= 0 by {
                    have -2147483648 <= to_integer(value) by {
                        normalize();
                    }
                    have ((-1 * to_integer(value)) + -to_integer(2147483648u64)) == (-2147483648 - to_integer(value)) by {
                        normalize();
                    }
                    apply(integer::le_difference(-2147483648, to_integer(value), ((-1 * to_integer(value)) + -to_integer(2147483648u64)))) using {
                        -2147483648 <= to_integer(value);
                        ((-1 * to_integer(value)) + -to_integer(2147483648u64)) == (-2147483648 -
                            to_integer(value));
                    };
                }
                have ((-1 * to_integer(amount)) + (-1 * to_integer(value)) + -to_integer(2147483648u64)) <= 0 by {
                    have ((-1 * to_integer(amount)) + ((-1 * to_integer(value)) + -to_integer(2147483648u64))) <= (0 + 0) by {
                        apply(integer::add_le((-1 * to_integer(amount)), 0, ((-1 * to_integer(value)) + -to_integer(2147483648u64)), 0)) using {
                            (-1 * to_integer(amount)) <= 0;
                            ((-1 * to_integer(value)) + -to_integer(2147483648u64)) <= 0;
                        };
                    }
                    have ((-1 * to_integer(amount)) + (-1 * to_integer(value)) + -to_integer(2147483648u64)) == ((-1 * to_integer(amount)) + ((-1 * to_integer(value)) + -to_integer(2147483648u64))) by {
                        normalize();
                    }
                    have (let integer_value: Integer = 0; integer_value) == (0 + 0) by {
                        normalize();
                    }
                    apply(integer::le_substitute(((-1 * to_integer(amount)) + ((-1 * to_integer(value)) + -to_integer(2147483648u64))), (0 + 0), ((-1 * to_integer(amount)) + (-1 * to_integer(value)) + -to_integer(2147483648u64)), 0)) using {
                        ((-1 * to_integer(amount)) + ((-1 * to_integer(value)) +
                            -to_integer(2147483648u64))) <= (0 + 0);
                        ((-1 * to_integer(amount)) + (-1 * to_integer(value)) +
                            -to_integer(2147483648u64)) == ((-1 * to_integer(amount)) + ((-1 *
                            to_integer(value)) + -to_integer(2147483648u64)));
                        (let integer_value: Integer = 0; integer_value) == (0 + 0);
                    };
                }
                have ((-1 * to_integer(amount)) + (-1 * to_integer(value)) + -to_integer(2147483648u64)) == (-2147483648 - (to_integer(value) + to_integer(amount))) by {
                    normalize();
                }
                apply(integer::difference_le(-2147483648, (to_integer(value) + to_integer(amount)), ((-1 * to_integer(amount)) + (-1 * to_integer(value)) + -to_integer(2147483648u64)))) using {
                    ((-1 * to_integer(amount)) + (-1 * to_integer(value)) + -to_integer(2147483648u64))
                        <= 0;
                    ((-1 * to_integer(amount)) + (-1 * to_integer(value)) + -to_integer(2147483648u64))
                        == (-2147483648 - (to_integer(value) + to_integer(amount)));
                };
            }
            normalize() using {
                -2147483648 <= (to_integer(value) + to_integer(amount));
            };
        }
        have (to_integer(value) + to_integer(amount)) <= 2147483647 by {
            have to_integer(value) <= 2147483647 - to_integer(amount) by {
                rewrite(2147483647 - to_integer(amount), to_integer(2147483647 - amount));
                known();
            }
            have to_integer(value) + to_integer(amount) <= (2147483647 - to_integer(amount)) + to_integer(amount) by {
                apply(integer::add_le(to_integer(value), 2147483647 - to_integer(amount), to_integer(amount), to_integer(amount))) using { to_integer(value) <= 2147483647 - to_integer(amount); to_integer(amount) <= to_integer(amount); };
            }
            have 2147483647 == (2147483647 - to_integer(amount)) + to_integer(amount) by normalize();
            apply(integer::le_substitute(to_integer(value) + to_integer(amount), (2147483647 - to_integer(amount)) + to_integer(amount), to_integer(value) + to_integer(amount), 2147483647)) using {
                to_integer(value) + to_integer(amount) <= (2147483647 - to_integer(amount)) + to_integer(amount);
                to_integer(value) + to_integer(amount) == to_integer(value) + to_integer(amount);
                2147483647 == (2147483647 - to_integer(amount)) + to_integer(amount);
            };
        }
        known();
    }
}

theorem int32_nonnegative_subtract_within_value_is_defined(value: int32, amount: int32) {
    requires 0 <= amount;
    requires amount <= value;

    ensures defined(value - amount) by {
        have to_integer(value) <= 2147483647 by {
            normalize();
        }
        have -2147483648 <= (to_integer(value) - to_integer(amount)) by {
            have -2147483648 <= (to_integer(value) - to_integer(amount)) by {
                have (to_integer((amount as int32)) + (-1 * to_integer((value as int32)))) <= 0 by {
                    have to_integer((amount as int32)) <= to_integer((value as int32)) by {
                        normalize() using {
                            amount <= value;
                        };
                    }
                    have (to_integer((amount as int32)) + (-1 * to_integer((value as int32)))) == (to_integer((amount as int32)) - to_integer((value as int32))) by {
                        normalize();
                    }
                    apply(integer::le_difference(to_integer((amount as int32)), to_integer((value as int32)), (to_integer((amount as int32)) + (-1 * to_integer((value as int32)))))) using {
                        to_integer((amount as int32)) <= to_integer((value as int32));
                        (to_integer((amount as int32)) + (-1 * to_integer((value as int32)))) ==
                            (to_integer((amount as int32)) - to_integer((value as int32)));
                    };
                }
                have (let integer_constant: Integer = -to_integer(2147483648u64); integer_constant) <= 0 by {
                    normalize();
                }
                have (to_integer((amount as int32)) + (-1 * to_integer((value as int32))) + -to_integer(2147483648u64)) <= 0 by {
                    have (to_integer((amount as int32)) + (-1 * to_integer((value as int32))) + (let integer_constant: Integer = -to_integer(2147483648u64); integer_constant)) <= (0 + 0) by {
                        apply(integer::add_le((to_integer((amount as int32)) + (-1 * to_integer((value as int32)))), 0, (let integer_constant: Integer = -to_integer(2147483648u64); integer_constant), 0)) using {
                            (to_integer((amount as int32)) + (-1 * to_integer((value as int32)))) <= 0;
                            (let integer_constant: Integer = -to_integer(2147483648u64);
                                integer_constant) <= 0;
                        };
                    }
                    have (to_integer((amount as int32)) + (-1 * to_integer((value as int32))) + -to_integer(2147483648u64)) == (to_integer((amount as int32)) + (-1 * to_integer((value as int32))) + (let integer_constant: Integer = -to_integer(2147483648u64); integer_constant)) by {
                        normalize();
                    }
                    have (let integer_value: Integer = 0; integer_value) == (0 + 0) by {
                        normalize();
                    }
                    apply(integer::le_substitute((to_integer((amount as int32)) + (-1 * to_integer((value as int32))) + (let integer_constant: Integer = -to_integer(2147483648u64); integer_constant)), (0 + 0), (to_integer((amount as int32)) + (-1 * to_integer((value as int32))) + -to_integer(2147483648u64)), 0)) using {
                        (to_integer((amount as int32)) + (-1 * to_integer((value as int32))) + (let
                            integer_constant: Integer = -to_integer(2147483648u64); integer_constant))
                            <= (0 + 0);
                        (to_integer((amount as int32)) + (-1 * to_integer((value as int32))) +
                            -to_integer(2147483648u64)) == (to_integer((amount as int32)) + (-1 *
                            to_integer((value as int32))) + (let integer_constant: Integer =
                            -to_integer(2147483648u64); integer_constant));
                        (let integer_value: Integer = 0; integer_value) == (0 + 0);
                    };
                }
                have (to_integer((amount as int32)) + (-1 * to_integer((value as int32))) + -to_integer(2147483648u64)) == (-2147483648 - (to_integer(value) - to_integer(amount))) by {
                    normalize();
                }
                apply(integer::difference_le(-2147483648, (to_integer(value) - to_integer(amount)), (to_integer((amount as int32)) + (-1 * to_integer((value as int32))) + -to_integer(2147483648u64)))) using {
                    (to_integer((amount as int32)) + (-1 * to_integer((value as int32))) +
                        -to_integer(2147483648u64)) <= 0;
                    (to_integer((amount as int32)) + (-1 * to_integer((value as int32))) +
                        -to_integer(2147483648u64)) == (-2147483648 - (to_integer(value) -
                        to_integer(amount)));
                };
            }
            normalize() using {
                -2147483648 <= (to_integer(value) - to_integer(amount));
            };
        }
        have (to_integer(value) - to_integer(amount)) <= 2147483647 by {
            have (to_integer(value) - to_integer(amount)) <= 2147483647 by {
                have (-1 * to_integer((amount as int32))) <= 0 by {
                    have 0 <= to_integer((amount as int32)) by {
                        normalize() using {
                            0 <= amount;
                        };
                    }
                    have (-1 * to_integer((amount as int32))) == (0 - to_integer((amount as int32))) by {
                        normalize();
                    }
                    apply(integer::le_difference(0, to_integer((amount as int32)), (-1 * to_integer((amount as int32))))) using {
                        0 <= to_integer((amount as int32));
                        (-1 * to_integer((amount as int32))) == (0 - to_integer((amount as int32)));
                    };
                }
                have (to_integer(value) + -2147483647) <= 0 by {
                    have (to_integer(value) + -2147483647) == (to_integer(value) - 2147483647) by {
                        normalize();
                    }
                    apply(integer::le_difference(to_integer(value), 2147483647, (to_integer(value) + -2147483647))) using {
                        to_integer(value) <= 2147483647;
                        (to_integer(value) + -2147483647) == (to_integer(value) - 2147483647);
                    };
                }
                have ((-1 * to_integer((amount as int32))) + to_integer(value) + -2147483647) <= 0 by {
                    have ((-1 * to_integer((amount as int32))) + (to_integer(value) + -2147483647)) <= (0 + 0) by {
                        apply(integer::add_le((-1 * to_integer((amount as int32))), 0, (to_integer(value) + -2147483647), 0)) using {
                            (-1 * to_integer((amount as int32))) <= 0;
                            (to_integer(value) + -2147483647) <= 0;
                        };
                    }
                    have ((-1 * to_integer((amount as int32))) + to_integer(value) + -2147483647) == ((-1 * to_integer((amount as int32))) + (to_integer(value) + -2147483647)) by {
                        normalize();
                    }
                    have (let integer_value: Integer = 0; integer_value) == (0 + 0) by {
                        normalize();
                    }
                    apply(integer::le_substitute(((-1 * to_integer((amount as int32))) + (to_integer(value) + -2147483647)), (0 + 0), ((-1 * to_integer((amount as int32))) + to_integer(value) + -2147483647), 0)) using {
                        ((-1 * to_integer((amount as int32))) + (to_integer(value) + -2147483647)) <= (0
                            + 0);
                        ((-1 * to_integer((amount as int32))) + to_integer(value) + -2147483647) == ((-1
                            * to_integer((amount as int32))) + (to_integer(value) + -2147483647));
                        (let integer_value: Integer = 0; integer_value) == (0 + 0);
                    };
                }
                have ((-1 * to_integer((amount as int32))) + to_integer(value) + -2147483647) == ((to_integer(value) - to_integer(amount)) - 2147483647) by {
                    normalize();
                }
                apply(integer::difference_le((to_integer(value) - to_integer(amount)), 2147483647, ((-1 * to_integer((amount as int32))) + to_integer(value) + -2147483647))) using {
                    ((-1 * to_integer((amount as int32))) + to_integer(value) + -2147483647) <= 0;
                    ((-1 * to_integer((amount as int32))) + to_integer(value) + -2147483647) ==
                        ((to_integer(value) - to_integer(amount)) - 2147483647);
                };
            }
            normalize() using {
                (to_integer(value) - to_integer(amount)) <= 2147483647;
            };
        }
        known();
    }
}

theorem int32_positive_predecessor_is_nonnegative(value: int32) {
    requires 0 < value;

    ensures 0 <= to_integer(value - 1) by {
        have 1 <= to_integer((value as int32)) by {
            normalize() using {
                ((0 as int32) as int32) < ((value as int32) as int32);
            };
        }
        have to_integer((value as int32)) <= 2147483647 by {
            normalize() using {
                ((0 as int32) as int32) < ((value as int32) as int32);
            };
        }
        have 1 <= to_integer((1 as int32)) by {
            normalize() using {};
        }
        have to_integer((1 as int32)) <= 1 by {
            normalize() using {};
        }
        have -2147483648 <= (to_integer((value as int32)) - to_integer((1 as int32))) by {
            have -2147483648 <= (to_integer((value as int32)) - to_integer((1 as int32))) by {
                have ((-1 * to_integer((value as int32))) + 1) <= 0 by {
                    have ((-1 * to_integer((value as int32))) + 1) == (1 - to_integer((value as int32))) by {
                        normalize();
                    }
                    apply(click::integer::le_difference(1, to_integer((value as int32)), ((-1 * to_integer((value as int32))) + 1))) using {
                        1 <= to_integer((value as int32));
                        ((-1 * to_integer((value as int32))) + 1) == (1 - to_integer((value as int32)));
                    };
                }
                have (let integer_constant: Integer = -to_integer(2147483648u64); integer_constant) <= 0 by {
                    normalize();
                }
                have ((-1 * to_integer((value as int32))) + -2147483647) <= 0 by {
                    have ((-1 * to_integer((value as int32))) + 1 + (let integer_constant: Integer = -to_integer(2147483648u64); integer_constant)) <= (0 + 0) by {
                        apply(click::integer::add_le(((-1 * to_integer((value as int32))) + 1), 0, (let integer_constant: Integer = -to_integer(2147483648u64); integer_constant), 0)) using {
                            ((-1 * to_integer((value as int32))) + 1) <= 0;
                            (let integer_constant: Integer = -to_integer(2147483648u64);
                                integer_constant) <= 0;
                        };
                    }
                    have ((-1 * to_integer((value as int32))) + -2147483647) == ((-1 * to_integer((value as int32))) + 1 + (let integer_constant: Integer = -to_integer(2147483648u64); integer_constant)) by {
                        normalize();
                    }
                    have (let integer_value: Integer = 0; integer_value) == (0 + 0) by {
                        normalize();
                    }
                    apply(click::integer::le_substitute(((-1 * to_integer((value as int32))) + 1 + (let integer_constant: Integer = -to_integer(2147483648u64); integer_constant)), (0 + 0), ((-1 * to_integer((value as int32))) + -2147483647), 0)) using {
                        ((-1 * to_integer((value as int32))) + 1 + (let integer_constant: Integer =
                            -to_integer(2147483648u64); integer_constant)) <= (0 + 0);
                        ((-1 * to_integer((value as int32))) + -2147483647) == ((-1 * to_integer((value
                            as int32))) + 1 + (let integer_constant: Integer =
                            -to_integer(2147483648u64); integer_constant));
                        (let integer_value: Integer = 0; integer_value) == (0 + 0);
                    };
                }
                have ((-1 * to_integer((value as int32))) + -2147483647) == (-2147483648 - (to_integer((value as int32)) - to_integer((1 as int32)))) by {
                    normalize();
                }
                apply(click::integer::difference_le(-2147483648, (to_integer((value as int32)) - to_integer((1 as int32))), ((-1 * to_integer((value as int32))) + -2147483647))) using {
                    ((-1 * to_integer((value as int32))) + -2147483647) <= 0;
                    ((-1 * to_integer((value as int32))) + -2147483647) == (-2147483648 -
                        (to_integer((value as int32)) - to_integer((1 as int32))));
                };
            }
            normalize() using {
                -2147483648 <= (to_integer((value as int32)) - to_integer((1 as int32)));
            };
        }
        have (to_integer((value as int32)) - to_integer((1 as int32))) <= 2147483647 by {
            have (to_integer((value as int32)) - to_integer((1 as int32))) <= 2147483647 by {
                have (to_integer((value as int32)) + -2147483647) <= 0 by {
                    have (to_integer((value as int32)) + -2147483647) == (to_integer((value as int32)) - 2147483647) by {
                        normalize();
                    }
                    apply(click::integer::le_difference(to_integer((value as int32)), 2147483647, (to_integer((value as int32)) + -2147483647))) using {
                        to_integer((value as int32)) <= 2147483647;
                        (to_integer((value as int32)) + -2147483647) == (to_integer((value as int32)) -
                            2147483647);
                    };
                }
                have (let integer_constant: Integer = -1; integer_constant) <= 0 by {
                    normalize();
                }
                have (to_integer((value as int32)) + -to_integer(2147483648u64)) <= 0 by {
                    have (to_integer((value as int32)) + -2147483647 + (let integer_constant: Integer = -1; integer_constant)) <= (0 + 0) by {
                        apply(click::integer::add_le((to_integer((value as int32)) + -2147483647), 0, (let integer_constant: Integer = -1; integer_constant), 0)) using {
                            (to_integer((value as int32)) + -2147483647) <= 0;
                            (let integer_constant: Integer = -1; integer_constant) <= 0;
                        };
                    }
                    have (to_integer((value as int32)) + -to_integer(2147483648u64)) == (to_integer((value as int32)) + -2147483647 + (let integer_constant: Integer = -1; integer_constant)) by {
                        normalize();
                    }
                    have (let integer_value: Integer = 0; integer_value) == (0 + 0) by {
                        normalize();
                    }
                    apply(click::integer::le_substitute((to_integer((value as int32)) + -2147483647 + (let integer_constant: Integer = -1; integer_constant)), (0 + 0), (to_integer((value as int32)) + -to_integer(2147483648u64)), 0)) using {
                        (to_integer((value as int32)) + -2147483647 + (let integer_constant: Integer =
                            -1; integer_constant)) <= (0 + 0);
                        (to_integer((value as int32)) + -to_integer(2147483648u64)) ==
                            (to_integer((value as int32)) + -2147483647 + (let integer_constant: Integer
                            = -1; integer_constant));
                        (let integer_value: Integer = 0; integer_value) == (0 + 0);
                    };
                }
                have (to_integer((value as int32)) + -to_integer(2147483648u64)) == ((to_integer((value as int32)) - to_integer((1 as int32))) - 2147483647) by {
                    normalize();
                }
                apply(click::integer::difference_le((to_integer((value as int32)) - to_integer((1 as int32))), 2147483647, (to_integer((value as int32)) + -to_integer(2147483648u64)))) using {
                    (to_integer((value as int32)) + -to_integer(2147483648u64)) <= 0;
                    (to_integer((value as int32)) + -to_integer(2147483648u64)) == ((to_integer((value
                        as int32)) - to_integer((1 as int32))) - 2147483647);
                };
            }
            normalize() using {
                (to_integer((value as int32)) - to_integer((1 as int32))) <= 2147483647;
            };
        }
        have defined((value - 1)) by {
            known();
        }
        have to_integer(((value - 1) as int32)) == (to_integer((value as int32)) - to_integer((1 as int32))) by {
            normalize() using {
                -2147483648 <= (to_integer((value as int32)) - to_integer((1 as int32)));
                (to_integer((value as int32)) - to_integer((1 as int32))) <= 2147483647;
            };
        }
        have 0 <= to_integer(((value - 1) as int32)) by {
            normalize() using {
                1 <= to_integer((value as int32));
                to_integer((value as int32)) <= 2147483647;
                1 <= to_integer((1 as int32));
                to_integer((1 as int32)) <= 1;
                1 <= to_integer((value as int32));
                to_integer((value as int32)) <= 2147483647;
                to_integer(((value - 1) as int32)) == (to_integer((value as int32)) - to_integer((1 as
                    int32)));
            };
        }
        have to_integer(((value - 1) as int32)) <= 2147483646 by {
            normalize() using {
                1 <= to_integer((value as int32));
                to_integer((value as int32)) <= 2147483647;
                1 <= to_integer((1 as int32));
                to_integer((1 as int32)) <= 1;
                1 <= to_integer((value as int32));
                to_integer((value as int32)) <= 2147483647;
                to_integer(((value - 1) as int32)) == (to_integer((value as int32)) - to_integer((1 as
                    int32)));
            };
        }
        have (0 as int32) <= ((value - 1) as int32) by {
            normalize() using {
                ((0 as int32) as int32) < ((value as int32) as int32);
                0 <= to_integer(((value - 1) as int32));
                to_integer(((value - 1) as int32)) <= 2147483646;
                to_integer(((value - 1) as int32)) == (to_integer((value as int32)) - to_integer((1 as
                    int32)));
            };
        }
        have 0 <= to_integer((value - 1)) by {
            normalize() using {
                (0 as int32) <= ((value - 1) as int32);
                to_integer(((value - 1) as int32)) == (to_integer((value as int32)) - to_integer((1 as
                    int32)));
            };
        }
        known();
    }
}

theorem int32_positive_predecessor_strictly_decreases(value: int32) {
    requires 0 < value;

    ensures to_integer(value - 1) < to_integer(value) by {
        have 1 <= to_integer((value as int32)) by {
            normalize() using {
                ((0 as int32) as int32) < ((value as int32) as int32);
            };
        }
        have to_integer((value as int32)) <= 2147483647 by {
            normalize() using {
                ((0 as int32) as int32) < ((value as int32) as int32);
            };
        }
        have 1 <= to_integer((1 as int32)) by {
            normalize() using {};
        }
        have to_integer((1 as int32)) <= 1 by {
            normalize() using {};
        }
        have -2147483648 <= (to_integer((value as int32)) - to_integer((1 as int32))) by {
            have -2147483648 <= (to_integer((value as int32)) - to_integer((1 as int32))) by {
                have ((-1 * to_integer((value as int32))) + 1) <= 0 by {
                    have ((-1 * to_integer((value as int32))) + 1) == (1 - to_integer((value as int32))) by {
                        normalize();
                    }
                    apply(click::integer::le_difference(1, to_integer((value as int32)), ((-1 * to_integer((value as int32))) + 1))) using {
                        1 <= to_integer((value as int32));
                        ((-1 * to_integer((value as int32))) + 1) == (1 - to_integer((value as int32)));
                    };
                }
                have (let integer_constant: Integer = -to_integer(2147483648u64); integer_constant) <= 0 by {
                    normalize();
                }
                have ((-1 * to_integer((value as int32))) + -2147483647) <= 0 by {
                    have ((-1 * to_integer((value as int32))) + 1 + (let integer_constant: Integer = -to_integer(2147483648u64); integer_constant)) <= (0 + 0) by {
                        apply(click::integer::add_le(((-1 * to_integer((value as int32))) + 1), 0, (let integer_constant: Integer = -to_integer(2147483648u64); integer_constant), 0)) using {
                            ((-1 * to_integer((value as int32))) + 1) <= 0;
                            (let integer_constant: Integer = -to_integer(2147483648u64);
                                integer_constant) <= 0;
                        };
                    }
                    have ((-1 * to_integer((value as int32))) + -2147483647) == ((-1 * to_integer((value as int32))) + 1 + (let integer_constant: Integer = -to_integer(2147483648u64); integer_constant)) by {
                        normalize();
                    }
                    have (let integer_value: Integer = 0; integer_value) == (0 + 0) by {
                        normalize();
                    }
                    apply(click::integer::le_substitute(((-1 * to_integer((value as int32))) + 1 + (let integer_constant: Integer = -to_integer(2147483648u64); integer_constant)), (0 + 0), ((-1 * to_integer((value as int32))) + -2147483647), 0)) using {
                        ((-1 * to_integer((value as int32))) + 1 + (let integer_constant: Integer =
                            -to_integer(2147483648u64); integer_constant)) <= (0 + 0);
                        ((-1 * to_integer((value as int32))) + -2147483647) == ((-1 * to_integer((value
                            as int32))) + 1 + (let integer_constant: Integer =
                            -to_integer(2147483648u64); integer_constant));
                        (let integer_value: Integer = 0; integer_value) == (0 + 0);
                    };
                }
                have ((-1 * to_integer((value as int32))) + -2147483647) == (-2147483648 - (to_integer((value as int32)) - to_integer((1 as int32)))) by {
                    normalize();
                }
                apply(click::integer::difference_le(-2147483648, (to_integer((value as int32)) - to_integer((1 as int32))), ((-1 * to_integer((value as int32))) + -2147483647))) using {
                    ((-1 * to_integer((value as int32))) + -2147483647) <= 0;
                    ((-1 * to_integer((value as int32))) + -2147483647) == (-2147483648 -
                        (to_integer((value as int32)) - to_integer((1 as int32))));
                };
            }
            normalize() using {
                -2147483648 <= (to_integer((value as int32)) - to_integer((1 as int32)));
            };
        }
        have (to_integer((value as int32)) - to_integer((1 as int32))) <= 2147483647 by {
            have (to_integer((value as int32)) - to_integer((1 as int32))) <= 2147483647 by {
                have (to_integer((value as int32)) + -2147483647) <= 0 by {
                    have (to_integer((value as int32)) + -2147483647) == (to_integer((value as int32)) - 2147483647) by {
                        normalize();
                    }
                    apply(click::integer::le_difference(to_integer((value as int32)), 2147483647, (to_integer((value as int32)) + -2147483647))) using {
                        to_integer((value as int32)) <= 2147483647;
                        (to_integer((value as int32)) + -2147483647) == (to_integer((value as int32)) -
                            2147483647);
                    };
                }
                have (let integer_constant: Integer = -1; integer_constant) <= 0 by {
                    normalize();
                }
                have (to_integer((value as int32)) + -to_integer(2147483648u64)) <= 0 by {
                    have (to_integer((value as int32)) + -2147483647 + (let integer_constant: Integer = -1; integer_constant)) <= (0 + 0) by {
                        apply(click::integer::add_le((to_integer((value as int32)) + -2147483647), 0, (let integer_constant: Integer = -1; integer_constant), 0)) using {
                            (to_integer((value as int32)) + -2147483647) <= 0;
                            (let integer_constant: Integer = -1; integer_constant) <= 0;
                        };
                    }
                    have (to_integer((value as int32)) + -to_integer(2147483648u64)) == (to_integer((value as int32)) + -2147483647 + (let integer_constant: Integer = -1; integer_constant)) by {
                        normalize();
                    }
                    have (let integer_value: Integer = 0; integer_value) == (0 + 0) by {
                        normalize();
                    }
                    apply(click::integer::le_substitute((to_integer((value as int32)) + -2147483647 + (let integer_constant: Integer = -1; integer_constant)), (0 + 0), (to_integer((value as int32)) + -to_integer(2147483648u64)), 0)) using {
                        (to_integer((value as int32)) + -2147483647 + (let integer_constant: Integer =
                            -1; integer_constant)) <= (0 + 0);
                        (to_integer((value as int32)) + -to_integer(2147483648u64)) ==
                            (to_integer((value as int32)) + -2147483647 + (let integer_constant: Integer
                            = -1; integer_constant));
                        (let integer_value: Integer = 0; integer_value) == (0 + 0);
                    };
                }
                have (to_integer((value as int32)) + -to_integer(2147483648u64)) == ((to_integer((value as int32)) - to_integer((1 as int32))) - 2147483647) by {
                    normalize();
                }
                apply(click::integer::difference_le((to_integer((value as int32)) - to_integer((1 as int32))), 2147483647, (to_integer((value as int32)) + -to_integer(2147483648u64)))) using {
                    (to_integer((value as int32)) + -to_integer(2147483648u64)) <= 0;
                    (to_integer((value as int32)) + -to_integer(2147483648u64)) == ((to_integer((value
                        as int32)) - to_integer((1 as int32))) - 2147483647);
                };
            }
            normalize() using {
                (to_integer((value as int32)) - to_integer((1 as int32))) <= 2147483647;
            };
        }
        have defined((value - 1)) by {
            known();
        }
        have to_integer(((value - 1) as int32)) == (to_integer((value as int32)) - to_integer((1 as int32))) by {
            normalize() using {
                -2147483648 <= (to_integer((value as int32)) - to_integer((1 as int32)));
                (to_integer((value as int32)) - to_integer((1 as int32))) <= 2147483647;
            };
        }
        have 0 <= to_integer(((value - 1) as int32)) by {
            normalize() using {
                1 <= to_integer((value as int32));
                to_integer((value as int32)) <= 2147483647;
                1 <= to_integer((1 as int32));
                to_integer((1 as int32)) <= 1;
                1 <= to_integer((value as int32));
                to_integer((value as int32)) <= 2147483647;
                to_integer(((value - 1) as int32)) == (to_integer((value as int32)) - to_integer((1 as
                    int32)));
            };
        }
        have to_integer(((value - 1) as int32)) <= 2147483646 by {
            normalize() using {
                1 <= to_integer((value as int32));
                to_integer((value as int32)) <= 2147483647;
                1 <= to_integer((1 as int32));
                to_integer((1 as int32)) <= 1;
                1 <= to_integer((value as int32));
                to_integer((value as int32)) <= 2147483647;
                to_integer(((value - 1) as int32)) == (to_integer((value as int32)) - to_integer((1 as
                    int32)));
            };
        }
        have 0 <= 0 by {
            normalize() using {
                to_integer(((value - 1) as int32)) == (to_integer((value as int32)) - to_integer((1 as
                    int32)));
            };
        }
        have ((value - 1) as int32) < (value as int32) by {
            have defined(((value - 1) as int32)) by {
                known();
            }
            have defined((value - 1)) by {
                known();
            }
            have defined(old(((value - 1) as int32))) by {
                known();
            }
            have defined(old((value - 1))) by {
                known();
            }
            have to_integer((((value - 1) as int32) as int32)) < to_integer(((value as int32) as int32)) by {
                have ((-1 * (to_integer((value as int32)) - to_integer((1 as int32)))) + to_integer(((value - 1) as int32))) == 0 by {
                    have (to_integer(((value - 1) as int32)) - (to_integer((value as int32)) - to_integer((1 as int32)))) == 0 by {
                        apply(click::integer::equal_difference(to_integer(((value - 1) as int32)), (to_integer((value as int32)) - to_integer((1 as int32))))) using {
                            to_integer(((value - 1) as int32)) == (to_integer((value as int32)) -
                                to_integer((1 as int32)));
                            defined(((value - 1) as int32));
                            defined((value - 1));
                            defined(old(((value - 1) as int32)));
                            defined(old((value - 1)));
                        };
                    }
                    have ((-1 * (to_integer((value as int32)) - to_integer((1 as int32)))) + to_integer(((value - 1) as int32))) == (to_integer(((value - 1) as int32)) - (to_integer((value as int32)) - to_integer((1 as int32)))) by {
                        normalize();
                    }
                    apply(click::integer::equal_substitute((to_integer(((value - 1) as int32)) - (to_integer((value as int32)) - to_integer((1 as int32)))), 0, ((-1 * (to_integer((value as int32)) - to_integer((1 as int32)))) + to_integer(((value - 1) as int32))), 0)) using {
                        (to_integer(((value - 1) as int32)) - (to_integer((value as int32)) -
                            to_integer((1 as int32)))) == 0;
                        ((-1 * (to_integer((value as int32)) - to_integer((1 as int32)))) +
                            to_integer(((value - 1) as int32))) == (to_integer(((value - 1) as int32)) -
                            (to_integer((value as int32)) - to_integer((1 as int32))));
                        (let integer_value: Integer = 0; integer_value) == 0;
                        defined(((value - 1) as int32));
                        defined((value - 1));
                        defined(old(((value - 1) as int32)));
                        defined(old((value - 1)));
                    };
                }
                have ((-1 * (to_integer((value as int32)) - to_integer((1 as int32)))) + to_integer(((value - 1) as int32))) <= 0 by {
                    apply(click::integer::equal_le(((-1 * (to_integer((value as int32)) - to_integer((1 as int32)))) + to_integer(((value - 1) as int32))), 0)) using {
                        ((-1 * (to_integer((value as int32)) - to_integer((1 as int32)))) +
                            to_integer(((value - 1) as int32))) == 0;
                        defined(((value - 1) as int32));
                        defined((value - 1));
                        defined(old(((value - 1) as int32)));
                        defined(old((value - 1)));
                    };
                }
                have ((-1 * (to_integer((value as int32)) - to_integer((1 as int32)))) + to_integer(((value - 1) as int32))) == ((to_integer((((value - 1) as int32) as int32)) + 1) - to_integer(((value as int32) as int32))) by {
                    normalize();
                }
                apply(click::integer::difference_le((to_integer((((value - 1) as int32) as int32)) + 1), to_integer(((value as int32) as int32)), ((-1 * (to_integer((value as int32)) - to_integer((1 as int32)))) + to_integer(((value - 1) as int32))))) using {
                    ((-1 * (to_integer((value as int32)) - to_integer((1 as int32)))) +
                        to_integer(((value - 1) as int32))) <= 0;
                    ((-1 * (to_integer((value as int32)) - to_integer((1 as int32)))) +
                        to_integer(((value - 1) as int32))) == ((to_integer((((value - 1) as int32) as
                        int32)) + 1) - to_integer(((value as int32) as int32)));
                    defined(((value - 1) as int32));
                    defined((value - 1));
                    defined(old(((value - 1) as int32)));
                    defined(old((value - 1)));
                };
                apply(click::integer::step_le_lt(to_integer((((value - 1) as int32) as int32)), to_integer(((value as int32) as int32)))) using {
                    (to_integer((((value - 1) as int32) as int32)) + 1) <= to_integer(((value as int32)
                        as int32));
                    defined(((value - 1) as int32));
                    defined((value - 1));
                    defined(old(((value - 1) as int32)));
                    defined(old((value - 1)));
                };
            }
            normalize() using {
                to_integer((((value - 1) as int32) as int32)) < to_integer(((value as int32) as int32));
            };
        }
        have to_integer((value - 1)) < to_integer(value) by {
            normalize() using {
                ((value - 1) as int32) < (value as int32);
                to_integer(((value - 1) as int32)) == (to_integer((value as int32)) - to_integer((1 as
                    int32)));
            };
        }
        known();
    }
}

theorem uint32_positive_predecessor_strictly_decreases(value: uint32) {
    requires 0u32 < value;

    ensures to_integer(value - 1u32) < to_integer(value) by {
        have 0 < to_integer(value) by {
            known();
        }
        have 0 <= (to_integer(value) - 1) by {
            have 0 <= (to_integer(value) - 1) by {
                have ((-1 * to_integer(value)) + 1) <= 0 by {
                    have (0 + 1) <= to_integer(value) by {
                        apply(integer::lt_step_le(0, to_integer(value))) using {
                            0 < to_integer(value);
                        };
                    }
                    have ((-1 * to_integer(value)) + 1) == ((0 + 1) - to_integer(value)) by {
                        normalize();
                    }
                    apply(integer::le_difference((0 + 1), to_integer(value), ((-1 * to_integer(value)) + 1))) using {
                        (0 + 1) <= to_integer(value);
                        ((-1 * to_integer(value)) + 1) == ((0 + 1) - to_integer(value));
                    };
                }
                have ((-1 * to_integer(value)) + 1) == (0 - (to_integer(value) - 1)) by {
                    normalize();
                }
                apply(integer::difference_le(0, (to_integer(value) - 1), ((-1 * to_integer(value)) + 1))) using {
                    ((-1 * to_integer(value)) + 1) <= 0;
                    ((-1 * to_integer(value)) + 1) == (0 - (to_integer(value) - 1));
                };
            }
            normalize() using {
                0 <= (to_integer(value) - 1);
            };
        }
        have (to_integer(value) - 1) <= 4294967295 by {
            have (to_integer(value) - 1) <= 4294967295 by {
                have (to_integer(value) + -to_integer(4294967295u64)) <= 0 by {
                    have to_integer(value) <= 4294967295 by {
                        normalize();
                    }
                    have (to_integer(value) + -to_integer(4294967295u64)) == (to_integer(value) - 4294967295) by {
                        normalize();
                    }
                    apply(integer::le_difference(to_integer(value), 4294967295, (to_integer(value) + -to_integer(4294967295u64)))) using {
                        to_integer(value) <= 4294967295;
                        (to_integer(value) + -to_integer(4294967295u64)) == (to_integer(value) -
                            4294967295);
                    };
                }
                have (let integer_constant: Integer = -1; integer_constant) <= 0 by {
                    normalize();
                }
                have (to_integer(value) + -to_integer(4294967296u64)) <= 0 by {
                    have (to_integer(value) + -to_integer(4294967295u64) + (let integer_constant: Integer = -1; integer_constant)) <= (0 + 0) by {
                        apply(integer::add_le((to_integer(value) + -to_integer(4294967295u64)), 0, (let integer_constant: Integer = -1; integer_constant), 0)) using {
                            (to_integer(value) + -to_integer(4294967295u64)) <= 0;
                            (let integer_constant: Integer = -1; integer_constant) <= 0;
                        };
                    }
                    have (to_integer(value) + -to_integer(4294967296u64)) == (to_integer(value) + -to_integer(4294967295u64) + (let integer_constant: Integer = -1; integer_constant)) by {
                        normalize();
                    }
                    have (let integer_value: Integer = 0; integer_value) == (0 + 0) by {
                        normalize();
                    }
                    apply(integer::le_substitute((to_integer(value) + -to_integer(4294967295u64) + (let integer_constant: Integer = -1; integer_constant)), (0 + 0), (to_integer(value) + -to_integer(4294967296u64)), 0)) using {
                        (to_integer(value) + -to_integer(4294967295u64) + (let integer_constant: Integer
                            = -1; integer_constant)) <= (0 + 0);
                        (to_integer(value) + -to_integer(4294967296u64)) == (to_integer(value) +
                            -to_integer(4294967295u64) + (let integer_constant: Integer = -1;
                            integer_constant));
                        (let integer_value: Integer = 0; integer_value) == (0 + 0);
                    };
                }
                have (to_integer(value) + -to_integer(4294967296u64)) == ((to_integer(value) - 1) - 4294967295) by {
                    normalize();
                }
                apply(integer::difference_le((to_integer(value) - 1), 4294967295, (to_integer(value) + -to_integer(4294967296u64)))) using {
                    (to_integer(value) + -to_integer(4294967296u64)) <= 0;
                    (to_integer(value) + -to_integer(4294967296u64)) == ((to_integer(value) - 1) -
                        4294967295);
                };
            }
            normalize() using {
                (to_integer(value) - 1) <= 4294967295;
            };
        }
        have to_integer((value - 1u32)) == (to_integer(value) - 1) by {
            normalize() using {
                0 <= (to_integer(value) - 1);
                (to_integer(value) - 1) <= 4294967295;
            };
        }
        have to_integer((value - 1u32)) < to_integer(value) by {
            have ((-1 * (to_integer(value) - 1)) + to_integer((value - 1u32))) == 0 by {
                have (to_integer((value - 1u32)) - (to_integer(value) - 1)) == 0 by {
                    apply(integer::equal_difference(to_integer((value - 1u32)), (to_integer(value) - 1))) using {
                        to_integer((value - 1u32)) == (to_integer(value) - 1);
                    };
                }
                have ((-1 * (to_integer(value) - 1)) + to_integer((value - 1u32))) == (to_integer((value - 1u32)) - (to_integer(value) - 1)) by {
                    normalize();
                }
                apply(integer::equal_substitute((to_integer((value - 1u32)) - (to_integer(value) - 1)), 0, ((-1 * (to_integer(value) - 1)) + to_integer((value - 1u32))), 0)) using {
                    (to_integer((value - 1u32)) - (to_integer(value) - 1)) == 0;
                    ((-1 * (to_integer(value) - 1)) + to_integer((value - 1u32))) == (to_integer((value
                        - 1u32)) - (to_integer(value) - 1));
                    (let integer_value: Integer = 0; integer_value) == 0;
                };
            }
            have ((-1 * (to_integer(value) - 1)) + to_integer((value - 1u32))) <= 0 by {
                apply(integer::equal_le(((-1 * (to_integer(value) - 1)) + to_integer((value - 1u32))), 0)) using {
                    ((-1 * (to_integer(value) - 1)) + to_integer((value - 1u32))) == 0;
                };
            }
            have ((-1 * (to_integer(value) - 1)) + to_integer((value - 1u32))) == ((to_integer((value - 1u32)) + 1) - to_integer(value)) by {
                normalize();
            }
            apply(integer::difference_le((to_integer((value - 1u32)) + 1), to_integer(value), ((-1 * (to_integer(value) - 1)) + to_integer((value - 1u32))))) using {
                ((-1 * (to_integer(value) - 1)) + to_integer((value - 1u32))) <= 0;
                ((-1 * (to_integer(value) - 1)) + to_integer((value - 1u32))) == ((to_integer((value -
                    1u32)) + 1) - to_integer(value));
            };
            apply(integer::step_le_lt(to_integer((value - 1u32)), to_integer(value))) using {
                (to_integer((value - 1u32)) + 1) <= to_integer(value);
            };
        }
        normalize() using {
            to_integer((value - 1u32)) < to_integer(value);
        };
    }
}

theorem uint32_increment_upper_bound(value: uint32, upper: uint32) {
    requires value < upper;

    ensures to_integer(value + 1u32) <= to_integer(upper) by {
        have to_integer(value) < to_integer(upper) by {
            known();
        }
        have 0 <= (to_integer(value) + 1) by {
            have 0 <= (to_integer(value) + 1) by {
                have (-1 * to_integer(value)) <= 0 by {
                    have 0 <= to_integer(value) by {
                        normalize();
                    }
                    have (-1 * to_integer(value)) == (0 - to_integer(value)) by {
                        normalize();
                    }
                    apply(integer::le_difference(0, to_integer(value), (-1 * to_integer(value)))) using {
                        0 <= to_integer(value);
                        (-1 * to_integer(value)) == (0 - to_integer(value));
                    };
                }
                have (let integer_constant: Integer = -1; integer_constant) <= 0 by {
                    normalize();
                }
                have ((-1 * to_integer(value)) + -1) <= 0 by {
                    have ((-1 * to_integer(value)) + (let integer_constant: Integer = -1; integer_constant)) <= (0 + 0) by {
                        apply(integer::add_le((-1 * to_integer(value)), 0, (let integer_constant: Integer = -1; integer_constant), 0)) using {
                            (-1 * to_integer(value)) <= 0;
                            (let integer_constant: Integer = -1; integer_constant) <= 0;
                        };
                    }
                    have ((-1 * to_integer(value)) + -1) == ((-1 * to_integer(value)) + (let integer_constant: Integer = -1; integer_constant)) by {
                        normalize();
                    }
                    have (let integer_value: Integer = 0; integer_value) == (0 + 0) by {
                        normalize();
                    }
                    apply(integer::le_substitute(((-1 * to_integer(value)) + (let integer_constant: Integer = -1; integer_constant)), (0 + 0), ((-1 * to_integer(value)) + -1), 0)) using {
                        ((-1 * to_integer(value)) + (let integer_constant: Integer = -1;
                            integer_constant)) <= (0 + 0);
                        ((-1 * to_integer(value)) + -1) == ((-1 * to_integer(value)) + (let
                            integer_constant: Integer = -1; integer_constant));
                        (let integer_value: Integer = 0; integer_value) == (0 + 0);
                    };
                }
                have ((-1 * to_integer(value)) + -1) == (0 - (to_integer(value) + 1)) by {
                    normalize();
                }
                apply(integer::difference_le(0, (to_integer(value) + 1), ((-1 * to_integer(value)) + -1))) using {
                    ((-1 * to_integer(value)) + -1) <= 0;
                    ((-1 * to_integer(value)) + -1) == (0 - (to_integer(value) + 1));
                };
            }
            normalize() using {
                0 <= (to_integer(value) + 1);
            };
        }
        have (to_integer(value) + 1) <= 4294967295 by {
            have (to_integer(value) + 1) <= 4294967295 by {
                have (to_integer(value) + (-1 * to_integer(upper)) + 1) <= 0 by {
                    have (to_integer(value) + 1) <= to_integer(upper) by {
                        apply(integer::lt_step_le(to_integer(value), to_integer(upper))) using {
                            to_integer(value) < to_integer(upper);
                        };
                    }
                    have (to_integer(value) + (-1 * to_integer(upper)) + 1) == ((to_integer(value) + 1) - to_integer(upper)) by {
                        normalize();
                    }
                    apply(integer::le_difference((to_integer(value) + 1), to_integer(upper), (to_integer(value) + (-1 * to_integer(upper)) + 1))) using {
                        (to_integer(value) + 1) <= to_integer(upper);
                        (to_integer(value) + (-1 * to_integer(upper)) + 1) == ((to_integer(value) + 1) -
                            to_integer(upper));
                    };
                }
                have (to_integer(upper) + -to_integer(4294967295u64)) <= 0 by {
                    have to_integer(upper) <= 4294967295 by {
                        normalize();
                    }
                    have (to_integer(upper) + -to_integer(4294967295u64)) == (to_integer(upper) - 4294967295) by {
                        normalize();
                    }
                    apply(integer::le_difference(to_integer(upper), 4294967295, (to_integer(upper) + -to_integer(4294967295u64)))) using {
                        to_integer(upper) <= 4294967295;
                        (to_integer(upper) + -to_integer(4294967295u64)) == (to_integer(upper) -
                            4294967295);
                    };
                }
                have (to_integer(value) + -to_integer(4294967294u64)) <= 0 by {
                    have (to_integer(value) + (-1 * to_integer(upper)) + 1 + (to_integer(upper) + -to_integer(4294967295u64))) <= (0 + 0) by {
                        apply(integer::add_le((to_integer(value) + (-1 * to_integer(upper)) + 1), 0, (to_integer(upper) + -to_integer(4294967295u64)), 0)) using {
                            (to_integer(value) + (-1 * to_integer(upper)) + 1) <= 0;
                            (to_integer(upper) + -to_integer(4294967295u64)) <= 0;
                        };
                    }
                    have (to_integer(value) + -to_integer(4294967294u64)) == (to_integer(value) + (-1 * to_integer(upper)) + 1 + (to_integer(upper) + -to_integer(4294967295u64))) by {
                        normalize();
                    }
                    have (let integer_value: Integer = 0; integer_value) == (0 + 0) by {
                        normalize();
                    }
                    apply(integer::le_substitute((to_integer(value) + (-1 * to_integer(upper)) + 1 + (to_integer(upper) + -to_integer(4294967295u64))), (0 + 0), (to_integer(value) + -to_integer(4294967294u64)), 0)) using {
                        (to_integer(value) + (-1 * to_integer(upper)) + 1 + (to_integer(upper) +
                            -to_integer(4294967295u64))) <= (0 + 0);
                        (to_integer(value) + -to_integer(4294967294u64)) == (to_integer(value) + (-1 *
                            to_integer(upper)) + 1 + (to_integer(upper) + -to_integer(4294967295u64)));
                        (let integer_value: Integer = 0; integer_value) == (0 + 0);
                    };
                }
                have (to_integer(value) + -to_integer(4294967294u64)) == ((to_integer(value) + 1) - 4294967295) by {
                    normalize();
                }
                apply(integer::difference_le((to_integer(value) + 1), 4294967295, (to_integer(value) + -to_integer(4294967294u64)))) using {
                    (to_integer(value) + -to_integer(4294967294u64)) <= 0;
                    (to_integer(value) + -to_integer(4294967294u64)) == ((to_integer(value) + 1) -
                        4294967295);
                };
            }
            normalize() using {
                (to_integer(value) + 1) <= 4294967295;
            };
        }
        have to_integer((value + 1u32)) == (to_integer(value) + 1) by {
            normalize() using {
                0 <= (to_integer(value) + 1);
                (to_integer(value) + 1) <= 4294967295;
            };
        }
        have to_integer((value + 1u32)) <= to_integer(upper) by {
            have ((-1 * (to_integer(value) + 1)) + to_integer((value + 1u32))) == 0 by {
                have (to_integer((value + 1u32)) - (to_integer(value) + 1)) == 0 by {
                    apply(integer::equal_difference(to_integer((value + 1u32)), (to_integer(value) + 1))) using {
                        to_integer((value + 1u32)) == (to_integer(value) + 1);
                    };
                }
                have ((-1 * (to_integer(value) + 1)) + to_integer((value + 1u32))) == (to_integer((value + 1u32)) - (to_integer(value) + 1)) by {
                    normalize();
                }
                apply(integer::equal_substitute((to_integer((value + 1u32)) - (to_integer(value) + 1)), 0, ((-1 * (to_integer(value) + 1)) + to_integer((value + 1u32))), 0)) using {
                    (to_integer((value + 1u32)) - (to_integer(value) + 1)) == 0;
                    ((-1 * (to_integer(value) + 1)) + to_integer((value + 1u32))) == (to_integer((value
                        + 1u32)) - (to_integer(value) + 1));
                    (let integer_value: Integer = 0; integer_value) == 0;
                };
            }
            have ((-1 * (to_integer(value) + 1)) + to_integer((value + 1u32))) <= 0 by {
                apply(integer::equal_le(((-1 * (to_integer(value) + 1)) + to_integer((value + 1u32))), 0)) using {
                    ((-1 * (to_integer(value) + 1)) + to_integer((value + 1u32))) == 0;
                };
            }
            have (to_integer(value) + (-1 * to_integer(upper)) + 1) <= 0 by {
                have (to_integer(value) + 1) <= to_integer(upper) by {
                    apply(integer::lt_step_le(to_integer(value), to_integer(upper))) using {
                        to_integer(value) < to_integer(upper);
                    };
                }
                have (to_integer(value) + (-1 * to_integer(upper)) + 1) == ((to_integer(value) + 1) - to_integer(upper)) by {
                    normalize();
                }
                apply(integer::le_difference((to_integer(value) + 1), to_integer(upper), (to_integer(value) + (-1 * to_integer(upper)) + 1))) using {
                    (to_integer(value) + 1) <= to_integer(upper);
                    (to_integer(value) + (-1 * to_integer(upper)) + 1) == ((to_integer(value) + 1) -
                        to_integer(upper));
                };
            }
            have (to_integer(value) + (-1 * (to_integer(value) + 1)) + (-1 * to_integer(upper)) + to_integer((value + 1u32)) + 1) <= 0 by {
                have ((-1 * (to_integer(value) + 1)) + to_integer((value + 1u32)) + (to_integer(value) + (-1 * to_integer(upper)) + 1)) <= (0 + 0) by {
                    apply(integer::add_le(((-1 * (to_integer(value) + 1)) + to_integer((value + 1u32))), 0, (to_integer(value) + (-1 * to_integer(upper)) + 1), 0)) using {
                        ((-1 * (to_integer(value) + 1)) + to_integer((value + 1u32))) <= 0;
                        (to_integer(value) + (-1 * to_integer(upper)) + 1) <= 0;
                    };
                }
                have (to_integer(value) + (-1 * (to_integer(value) + 1)) + (-1 * to_integer(upper)) + to_integer((value + 1u32)) + 1) == ((-1 * (to_integer(value) + 1)) + to_integer((value + 1u32)) + (to_integer(value) + (-1 * to_integer(upper)) + 1)) by {
                    normalize();
                }
                have (let integer_value: Integer = 0; integer_value) == (0 + 0) by {
                    normalize();
                }
                apply(integer::le_substitute(((-1 * (to_integer(value) + 1)) + to_integer((value + 1u32)) + (to_integer(value) + (-1 * to_integer(upper)) + 1)), (0 + 0), (to_integer(value) + (-1 * (to_integer(value) + 1)) + (-1 * to_integer(upper)) + to_integer((value + 1u32)) + 1), 0)) using {
                    ((-1 * (to_integer(value) + 1)) + to_integer((value + 1u32)) + (to_integer(value) +
                        (-1 * to_integer(upper)) + 1)) <= (0 + 0);
                    (to_integer(value) + (-1 * (to_integer(value) + 1)) + (-1 * to_integer(upper)) +
                        to_integer((value + 1u32)) + 1) == ((-1 * (to_integer(value) + 1)) +
                        to_integer((value + 1u32)) + (to_integer(value) + (-1 * to_integer(upper)) +
                        1));
                    (let integer_value: Integer = 0; integer_value) == (0 + 0);
                };
            }
            have (to_integer(value) + (-1 * (to_integer(value) + 1)) + (-1 * to_integer(upper)) + to_integer((value + 1u32)) + 1) == (to_integer((value + 1u32)) - to_integer(upper)) by {
                normalize();
            }
            apply(integer::difference_le(to_integer((value + 1u32)), to_integer(upper), (to_integer(value) + (-1 * (to_integer(value) + 1)) + (-1 * to_integer(upper)) + to_integer((value + 1u32)) + 1))) using {
                (to_integer(value) + (-1 * (to_integer(value) + 1)) + (-1 * to_integer(upper)) +
                    to_integer((value + 1u32)) + 1) <= 0;
                (to_integer(value) + (-1 * (to_integer(value) + 1)) + (-1 * to_integer(upper)) +
                    to_integer((value + 1u32)) + 1) == (to_integer((value + 1u32)) - to_integer(upper));
            };
        }
        normalize() using {
            to_integer((value + 1u32)) <= to_integer(upper);
        };
    }
}

theorem uint32_less_than_implies_positive_difference(value: uint32, upper: uint32) {
    requires value < upper;

    ensures 0 < to_integer(upper - value) by {
        have 0 <= (to_integer(upper) - to_integer(value)) by {
            have 0 <= (to_integer(upper) - to_integer(value)) by {
                have (to_integer(value) + (-1 * to_integer(upper)) + 1) <= 0 by {
                    have (to_integer(value) + 1) <= to_integer(upper) by {
                        apply(integer::lt_step_le(to_integer(value), to_integer(upper))) using {
                            to_integer(value) < to_integer(upper);
                        };
                    }
                    have (to_integer(value) + (-1 * to_integer(upper)) + 1) == ((to_integer(value) + 1) - to_integer(upper)) by {
                        normalize();
                    }
                    apply(integer::le_difference((to_integer(value) + 1), to_integer(upper), (to_integer(value) + (-1 * to_integer(upper)) + 1))) using {
                        (to_integer(value) + 1) <= to_integer(upper);
                        (to_integer(value) + (-1 * to_integer(upper)) + 1) == ((to_integer(value) + 1) -
                            to_integer(upper));
                    };
                }
                have (let integer_constant: Integer = -1; integer_constant) <= 0 by {
                    normalize();
                }
                have (to_integer(value) + (-1 * to_integer(upper))) <= 0 by {
                    have (to_integer(value) + (-1 * to_integer(upper)) + 1 + (let integer_constant: Integer = -1; integer_constant)) <= (0 + 0) by {
                        apply(integer::add_le((to_integer(value) + (-1 * to_integer(upper)) + 1), 0, (let integer_constant: Integer = -1; integer_constant), 0)) using {
                            (to_integer(value) + (-1 * to_integer(upper)) + 1) <= 0;
                            (let integer_constant: Integer = -1; integer_constant) <= 0;
                        };
                    }
                    have (to_integer(value) + (-1 * to_integer(upper))) == (to_integer(value) + (-1 * to_integer(upper)) + 1 + (let integer_constant: Integer = -1; integer_constant)) by {
                        normalize();
                    }
                    have (let integer_value: Integer = 0; integer_value) == (0 + 0) by {
                        normalize();
                    }
                    apply(integer::le_substitute((to_integer(value) + (-1 * to_integer(upper)) + 1 + (let integer_constant: Integer = -1; integer_constant)), (0 + 0), (to_integer(value) + (-1 * to_integer(upper))), 0)) using {
                        (to_integer(value) + (-1 * to_integer(upper)) + 1 + (let integer_constant:
                            Integer = -1; integer_constant)) <= (0 + 0);
                        (to_integer(value) + (-1 * to_integer(upper))) == (to_integer(value) + (-1 *
                            to_integer(upper)) + 1 + (let integer_constant: Integer = -1;
                            integer_constant));
                        (let integer_value: Integer = 0; integer_value) == (0 + 0);
                    };
                }
                have (to_integer(value) + (-1 * to_integer(upper))) == (0 - (to_integer(upper) - to_integer(value))) by {
                    normalize();
                }
                apply(integer::difference_le(0, (to_integer(upper) - to_integer(value)), (to_integer(value) + (-1 * to_integer(upper))))) using {
                    (to_integer(value) + (-1 * to_integer(upper))) <= 0;
                    (to_integer(value) + (-1 * to_integer(upper))) == (0 - (to_integer(upper) -
                        to_integer(value)));
                };
            }
            normalize() using {
                0 <= (to_integer(upper) - to_integer(value));
            };
        }
        have (to_integer(upper) - to_integer(value)) <= 4294967295 by {
            have (to_integer(upper) - to_integer(value)) <= 4294967295 by {
                have (to_integer(upper) + -to_integer(4294967295u64)) <= 0 by {
                    have to_integer(upper) <= 4294967295 by {
                        normalize();
                    }
                    have (to_integer(upper) + -to_integer(4294967295u64)) == (to_integer(upper) - 4294967295) by {
                        normalize();
                    }
                    apply(integer::le_difference(to_integer(upper), 4294967295, (to_integer(upper) + -to_integer(4294967295u64)))) using {
                        to_integer(upper) <= 4294967295;
                        (to_integer(upper) + -to_integer(4294967295u64)) == (to_integer(upper) -
                            4294967295);
                    };
                }
                have (-1 * to_integer(value)) <= 0 by {
                    have 0 <= to_integer(value) by {
                        normalize();
                    }
                    have (-1 * to_integer(value)) == (0 - to_integer(value)) by {
                        normalize();
                    }
                    apply(integer::le_difference(0, to_integer(value), (-1 * to_integer(value)))) using {
                        0 <= to_integer(value);
                        (-1 * to_integer(value)) == (0 - to_integer(value));
                    };
                }
                have ((-1 * to_integer(value)) + to_integer(upper) + -to_integer(4294967295u64)) <= 0 by {
                    have (to_integer(upper) + -to_integer(4294967295u64) + (-1 * to_integer(value))) <= (0 + 0) by {
                        apply(integer::add_le((to_integer(upper) + -to_integer(4294967295u64)), 0, (-1 * to_integer(value)), 0)) using {
                            (to_integer(upper) + -to_integer(4294967295u64)) <= 0;
                            (-1 * to_integer(value)) <= 0;
                        };
                    }
                    have ((-1 * to_integer(value)) + to_integer(upper) + -to_integer(4294967295u64)) == (to_integer(upper) + -to_integer(4294967295u64) + (-1 * to_integer(value))) by {
                        normalize();
                    }
                    have (let integer_value: Integer = 0; integer_value) == (0 + 0) by {
                        normalize();
                    }
                    apply(integer::le_substitute((to_integer(upper) + -to_integer(4294967295u64) + (-1 * to_integer(value))), (0 + 0), ((-1 * to_integer(value)) + to_integer(upper) + -to_integer(4294967295u64)), 0)) using {
                        (to_integer(upper) + -to_integer(4294967295u64) + (-1 * to_integer(value))) <=
                            (0 + 0);
                        ((-1 * to_integer(value)) + to_integer(upper) + -to_integer(4294967295u64)) ==
                            (to_integer(upper) + -to_integer(4294967295u64) + (-1 * to_integer(value)));
                        (let integer_value: Integer = 0; integer_value) == (0 + 0);
                    };
                }
                have ((-1 * to_integer(value)) + to_integer(upper) + -to_integer(4294967295u64)) == ((to_integer(upper) - to_integer(value)) - 4294967295) by {
                    normalize();
                }
                apply(integer::difference_le((to_integer(upper) - to_integer(value)), 4294967295, ((-1 * to_integer(value)) + to_integer(upper) + -to_integer(4294967295u64)))) using {
                    ((-1 * to_integer(value)) + to_integer(upper) + -to_integer(4294967295u64)) <= 0;
                    ((-1 * to_integer(value)) + to_integer(upper) + -to_integer(4294967295u64)) ==
                        ((to_integer(upper) - to_integer(value)) - 4294967295);
                };
            }
            normalize() using {
                (to_integer(upper) - to_integer(value)) <= 4294967295;
            };
        }
        have to_integer((upper - value)) == (to_integer(upper) - to_integer(value)) by {
            normalize() using {
                0 <= (to_integer(upper) - to_integer(value));
                (to_integer(upper) - to_integer(value)) <= 4294967295;
            };
        }
        have 0 < to_integer((upper - value)) by {
            have ((-1 * (to_integer(upper) - to_integer(value))) + to_integer((upper - value))) == 0 by {
                have (to_integer((upper - value)) - (to_integer(upper) - to_integer(value))) == 0 by {
                    apply(integer::equal_difference(to_integer((upper - value)), (to_integer(upper) - to_integer(value)))) using {
                        to_integer((upper - value)) == (to_integer(upper) - to_integer(value));
                    };
                }
                have ((-1 * (to_integer(upper) - to_integer(value))) + to_integer((upper - value))) == (to_integer((upper - value)) - (to_integer(upper) - to_integer(value))) by {
                    normalize();
                }
                apply(integer::equal_substitute((to_integer((upper - value)) - (to_integer(upper) - to_integer(value))), 0, ((-1 * (to_integer(upper) - to_integer(value))) + to_integer((upper - value))), 0)) using {
                    (to_integer((upper - value)) - (to_integer(upper) - to_integer(value))) == 0;
                    ((-1 * (to_integer(upper) - to_integer(value))) + to_integer((upper - value))) ==
                        (to_integer((upper - value)) - (to_integer(upper) - to_integer(value)));
                    (let integer_value: Integer = 0; integer_value) == 0;
                };
            }
            have ((to_integer(upper) - to_integer(value)) + (-1 * to_integer((upper - value)))) <= 0 by {
                have (((-1 * (to_integer(upper) - to_integer(value))) + to_integer((upper - value))) * -1) == (0 * -1) by {
                    apply(integer::equal_multiply(((-1 * (to_integer(upper) - to_integer(value))) + to_integer((upper - value))), 0, -1)) using {
                        ((-1 * (to_integer(upper) - to_integer(value))) + to_integer((upper - value)))
                            == 0;
                    };
                }
                have ((to_integer(upper) - to_integer(value)) + (-1 * to_integer((upper - value)))) == 0 by {
                    have ((to_integer(upper) - to_integer(value)) + (-1 * to_integer((upper - value)))) == (((-1 * (to_integer(upper) - to_integer(value))) + to_integer((upper - value))) * -1) by {
                        normalize();
                    }
                    have (let integer_value: Integer = 0; integer_value) == (0 * -1) by {
                        normalize();
                    }
                    apply(integer::equal_substitute((((-1 * (to_integer(upper) - to_integer(value))) + to_integer((upper - value))) * -1), (0 * -1), ((to_integer(upper) - to_integer(value)) + (-1 * to_integer((upper - value)))), 0)) using {
                        (((-1 * (to_integer(upper) - to_integer(value))) + to_integer((upper - value)))
                            * -1) == (0 * -1);
                        ((to_integer(upper) - to_integer(value)) + (-1 * to_integer((upper - value))))
                            == (((-1 * (to_integer(upper) - to_integer(value))) + to_integer((upper -
                            value))) * -1);
                        (let integer_value: Integer = 0; integer_value) == (0 * -1);
                    };
                }
                apply(integer::equal_le(((to_integer(upper) - to_integer(value)) + (-1 * to_integer((upper - value)))), 0)) using {
                    ((to_integer(upper) - to_integer(value)) + (-1 * to_integer((upper - value)))) == 0;
                };
            }
            have (to_integer(value) + (-1 * to_integer(upper)) + 1) <= 0 by {
                have (to_integer(value) + 1) <= to_integer(upper) by {
                    apply(integer::lt_step_le(to_integer(value), to_integer(upper))) using {
                        to_integer(value) < to_integer(upper);
                    };
                }
                have (to_integer(value) + (-1 * to_integer(upper)) + 1) == ((to_integer(value) + 1) - to_integer(upper)) by {
                    normalize();
                }
                apply(integer::le_difference((to_integer(value) + 1), to_integer(upper), (to_integer(value) + (-1 * to_integer(upper)) + 1))) using {
                    (to_integer(value) + 1) <= to_integer(upper);
                    (to_integer(value) + (-1 * to_integer(upper)) + 1) == ((to_integer(value) + 1) -
                        to_integer(upper));
                };
            }
            have (to_integer(value) + (-1 * to_integer(upper)) + (to_integer(upper) - to_integer(value)) + (-1 * to_integer((upper - value))) + 1) <= 0 by {
                have ((to_integer(upper) - to_integer(value)) + (-1 * to_integer((upper - value))) + (to_integer(value) + (-1 * to_integer(upper)) + 1)) <= (0 + 0) by {
                    apply(integer::add_le(((to_integer(upper) - to_integer(value)) + (-1 * to_integer((upper - value)))), 0, (to_integer(value) + (-1 * to_integer(upper)) + 1), 0)) using {
                        ((to_integer(upper) - to_integer(value)) + (-1 * to_integer((upper - value))))
                            <= 0;
                        (to_integer(value) + (-1 * to_integer(upper)) + 1) <= 0;
                    };
                }
                have (to_integer(value) + (-1 * to_integer(upper)) + (to_integer(upper) - to_integer(value)) + (-1 * to_integer((upper - value))) + 1) == ((to_integer(upper) - to_integer(value)) + (-1 * to_integer((upper - value))) + (to_integer(value) + (-1 * to_integer(upper)) + 1)) by {
                    normalize();
                }
                have (let integer_value: Integer = 0; integer_value) == (0 + 0) by {
                    normalize();
                }
                apply(integer::le_substitute(((to_integer(upper) - to_integer(value)) + (-1 * to_integer((upper - value))) + (to_integer(value) + (-1 * to_integer(upper)) + 1)), (0 + 0), (to_integer(value) + (-1 * to_integer(upper)) + (to_integer(upper) - to_integer(value)) + (-1 * to_integer((upper - value))) + 1), 0)) using {
                    ((to_integer(upper) - to_integer(value)) + (-1 * to_integer((upper - value))) +
                        (to_integer(value) + (-1 * to_integer(upper)) + 1)) <= (0 + 0);
                    (to_integer(value) + (-1 * to_integer(upper)) + (to_integer(upper) -
                        to_integer(value)) + (-1 * to_integer((upper - value))) + 1) ==
                        ((to_integer(upper) - to_integer(value)) + (-1 * to_integer((upper - value))) +
                        (to_integer(value) + (-1 * to_integer(upper)) + 1));
                    (let integer_value: Integer = 0; integer_value) == (0 + 0);
                };
            }
            have (to_integer(value) + (-1 * to_integer(upper)) + (to_integer(upper) - to_integer(value)) + (-1 * to_integer((upper - value))) + 1) == ((0 + 1) - to_integer((upper - value))) by {
                normalize();
            }
            apply(integer::difference_le((0 + 1), to_integer((upper - value)), (to_integer(value) + (-1 * to_integer(upper)) + (to_integer(upper) - to_integer(value)) + (-1 * to_integer((upper - value))) + 1))) using {
                (to_integer(value) + (-1 * to_integer(upper)) + (to_integer(upper) - to_integer(value))
                    + (-1 * to_integer((upper - value))) + 1) <= 0;
                (to_integer(value) + (-1 * to_integer(upper)) + (to_integer(upper) - to_integer(value))
                    + (-1 * to_integer((upper - value))) + 1) == ((0 + 1) - to_integer((upper -
                    value)));
            };
            apply(integer::step_le_lt(0, to_integer((upper - value)))) using {
                (0 + 1) <= to_integer((upper - value));
            };
        }
        normalize() using {
            0 < to_integer((upper - value));
        };
    }
}

// Neither `bound - value` nor `(bound - 1) - value` wraps under
// `value < bound`, so the measure drops by exactly one.
axiom uint32_difference_decreases_after_increment(value: uint32, bound: uint32) {
    requires value < bound;
    ensures to_integer((0u32 - value) + (bound - 1u32)) < to_integer((0u32 - value) + bound);
}

theorem int32_nonnegative_predecessor_upper_bound(value: int32, bound: int32) {
    requires 0 <= value;
    requires value <= bound;

    ensures to_integer(value - 1) <= to_integer(bound) by {
        have 0 <= to_integer((value as int32)) by {
            normalize() using {
                ((0 as int32) as int32) <= ((value as int32) as int32);
            };
        }
        have to_integer((value as int32)) <= 2147483647 by {
            normalize() using {
                ((0 as int32) as int32) <= ((value as int32) as int32);
            };
        }
        have 1 <= to_integer((1 as int32)) by {
            normalize() using {};
        }
        have to_integer((1 as int32)) <= 1 by {
            normalize() using {};
        }
        have -2147483648 <= (to_integer((value as int32)) - to_integer((1 as int32))) by {
            have -2147483648 <= (to_integer((value as int32)) - to_integer((1 as int32))) by {
                have (-1 * to_integer((value as int32))) <= 0 by {
                    have (-1 * to_integer((value as int32))) == (0 - to_integer((value as int32))) by {
                        normalize();
                    }
                    apply(click::integer::le_difference(0, to_integer((value as int32)), (-1 * to_integer((value as int32))))) using {
                        0 <= to_integer((value as int32));
                        (-1 * to_integer((value as int32))) == (0 - to_integer((value as int32)));
                    };
                }
                have (let integer_constant: Integer = -2147483647; integer_constant) <= 0 by {
                    normalize();
                }
                have ((-1 * to_integer((value as int32))) + -2147483647) <= 0 by {
                    have ((-1 * to_integer((value as int32))) + (let integer_constant: Integer = -2147483647; integer_constant)) <= (0 + 0) by {
                        apply(click::integer::add_le((-1 * to_integer((value as int32))), 0, (let integer_constant: Integer = -2147483647; integer_constant), 0)) using {
                            (-1 * to_integer((value as int32))) <= 0;
                            (let integer_constant: Integer = -2147483647; integer_constant) <= 0;
                        };
                    }
                    have ((-1 * to_integer((value as int32))) + -2147483647) == ((-1 * to_integer((value as int32))) + (let integer_constant: Integer = -2147483647; integer_constant)) by {
                        normalize();
                    }
                    have (let integer_value: Integer = 0; integer_value) == (0 + 0) by {
                        normalize();
                    }
                    apply(click::integer::le_substitute(((-1 * to_integer((value as int32))) + (let integer_constant: Integer = -2147483647; integer_constant)), (0 + 0), ((-1 * to_integer((value as int32))) + -2147483647), 0)) using {
                        ((-1 * to_integer((value as int32))) + (let integer_constant: Integer =
                            -2147483647; integer_constant)) <= (0 + 0);
                        ((-1 * to_integer((value as int32))) + -2147483647) == ((-1 * to_integer((value
                            as int32))) + (let integer_constant: Integer = -2147483647;
                            integer_constant));
                        (let integer_value: Integer = 0; integer_value) == (0 + 0);
                    };
                }
                have ((-1 * to_integer((value as int32))) + -2147483647) == (-2147483648 - (to_integer((value as int32)) - to_integer((1 as int32)))) by {
                    normalize();
                }
                apply(click::integer::difference_le(-2147483648, (to_integer((value as int32)) - to_integer((1 as int32))), ((-1 * to_integer((value as int32))) + -2147483647))) using {
                    ((-1 * to_integer((value as int32))) + -2147483647) <= 0;
                    ((-1 * to_integer((value as int32))) + -2147483647) == (-2147483648 -
                        (to_integer((value as int32)) - to_integer((1 as int32))));
                };
            }
            normalize() using {
                -2147483648 <= (to_integer((value as int32)) - to_integer((1 as int32)));
            };
        }
        have (to_integer((value as int32)) - to_integer((1 as int32))) <= 2147483647 by {
            have (to_integer((value as int32)) - to_integer((1 as int32))) <= 2147483647 by {
                have (to_integer((value as int32)) + -2147483647) <= 0 by {
                    have (to_integer((value as int32)) + -2147483647) == (to_integer((value as int32)) - 2147483647) by {
                        normalize();
                    }
                    apply(click::integer::le_difference(to_integer((value as int32)), 2147483647, (to_integer((value as int32)) + -2147483647))) using {
                        to_integer((value as int32)) <= 2147483647;
                        (to_integer((value as int32)) + -2147483647) == (to_integer((value as int32)) -
                            2147483647);
                    };
                }
                have (let integer_constant: Integer = -1; integer_constant) <= 0 by {
                    normalize();
                }
                have (to_integer((value as int32)) + -to_integer(2147483648u64)) <= 0 by {
                    have (to_integer((value as int32)) + -2147483647 + (let integer_constant: Integer = -1; integer_constant)) <= (0 + 0) by {
                        apply(click::integer::add_le((to_integer((value as int32)) + -2147483647), 0, (let integer_constant: Integer = -1; integer_constant), 0)) using {
                            (to_integer((value as int32)) + -2147483647) <= 0;
                            (let integer_constant: Integer = -1; integer_constant) <= 0;
                        };
                    }
                    have (to_integer((value as int32)) + -to_integer(2147483648u64)) == (to_integer((value as int32)) + -2147483647 + (let integer_constant: Integer = -1; integer_constant)) by {
                        normalize();
                    }
                    have (let integer_value: Integer = 0; integer_value) == (0 + 0) by {
                        normalize();
                    }
                    apply(click::integer::le_substitute((to_integer((value as int32)) + -2147483647 + (let integer_constant: Integer = -1; integer_constant)), (0 + 0), (to_integer((value as int32)) + -to_integer(2147483648u64)), 0)) using {
                        (to_integer((value as int32)) + -2147483647 + (let integer_constant: Integer =
                            -1; integer_constant)) <= (0 + 0);
                        (to_integer((value as int32)) + -to_integer(2147483648u64)) ==
                            (to_integer((value as int32)) + -2147483647 + (let integer_constant: Integer
                            = -1; integer_constant));
                        (let integer_value: Integer = 0; integer_value) == (0 + 0);
                    };
                }
                have (to_integer((value as int32)) + -to_integer(2147483648u64)) == ((to_integer((value as int32)) - to_integer((1 as int32))) - 2147483647) by {
                    normalize();
                }
                apply(click::integer::difference_le((to_integer((value as int32)) - to_integer((1 as int32))), 2147483647, (to_integer((value as int32)) + -to_integer(2147483648u64)))) using {
                    (to_integer((value as int32)) + -to_integer(2147483648u64)) <= 0;
                    (to_integer((value as int32)) + -to_integer(2147483648u64)) == ((to_integer((value
                        as int32)) - to_integer((1 as int32))) - 2147483647);
                };
            }
            normalize() using {
                (to_integer((value as int32)) - to_integer((1 as int32))) <= 2147483647;
            };
        }
        have defined((value - 1)) by {
            known();
        }
        have to_integer(((value - 1) as int32)) == (to_integer((value as int32)) - to_integer((1 as int32))) by {
            normalize() using {
                -2147483648 <= (to_integer((value as int32)) - to_integer((1 as int32)));
                (to_integer((value as int32)) - to_integer((1 as int32))) <= 2147483647;
            };
        }
        have -1 <= to_integer(((value - 1) as int32)) by {
            normalize() using {
                0 <= to_integer((value as int32));
                to_integer((value as int32)) <= 2147483647;
                1 <= to_integer((1 as int32));
                to_integer((1 as int32)) <= 1;
                0 <= to_integer((value as int32));
                to_integer((value as int32)) <= 2147483647;
                to_integer(((value - 1) as int32)) == (to_integer((value as int32)) - to_integer((1 as
                    int32)));
            };
        }
        have to_integer(((value - 1) as int32)) <= 2147483646 by {
            normalize() using {
                0 <= to_integer((value as int32));
                to_integer((value as int32)) <= 2147483647;
                1 <= to_integer((1 as int32));
                to_integer((1 as int32)) <= 1;
                0 <= to_integer((value as int32));
                to_integer((value as int32)) <= 2147483647;
                to_integer(((value - 1) as int32)) == (to_integer((value as int32)) - to_integer((1 as
                    int32)));
            };
        }
        have -1 <= 0 by {
            normalize() using {
                to_integer(((value - 1) as int32)) == (to_integer((value as int32)) - to_integer((1 as
                    int32)));
            };
        }
        have (to_integer(((value as int32) as int32)) + -1) <= (to_integer(((bound as int32) as int32)) + 0) by {
            have defined(((value - 1) as int32)) by {
                known();
            }
            have defined((value - 1)) by {
                known();
            }
            have defined(old(((value - 1) as int32))) by {
                known();
            }
            have defined(old((value - 1))) by {
                known();
            }
            have (to_integer(((value as int32) as int32)) + -1) <= (to_integer(((bound as int32) as int32)) + 0) by {
                have (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((bound as int32) as int32) as int32)))) <= 0 by {
                    have to_integer((((value as int32) as int32) as int32)) <= to_integer((((bound as int32) as int32) as int32)) by {
                        normalize() using {
                            ((value as int32) as int32) <= ((bound as int32) as int32);
                        };
                    }
                    have (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((bound as int32) as int32) as int32)))) == (to_integer((((value as int32) as int32) as int32)) - to_integer((((bound as int32) as int32) as int32))) by {
                        normalize();
                    }
                    apply(click::integer::le_difference(to_integer((((value as int32) as int32) as int32)), to_integer((((bound as int32) as int32) as int32)), (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((bound as int32) as int32) as int32)))))) using {
                        to_integer((((value as int32) as int32) as int32)) <= to_integer((((bound as
                            int32) as int32) as int32));
                        (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((bound
                            as int32) as int32) as int32)))) == (to_integer((((value as int32) as int32)
                            as int32)) - to_integer((((bound as int32) as int32) as int32)));
                        defined(((value - 1) as int32));
                        defined((value - 1));
                        defined(old(((value - 1) as int32)));
                        defined(old((value - 1)));
                    };
                }
                have (let integer_constant: Integer = -1; integer_constant) <= 0 by {
                    normalize();
                }
                have (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((bound as int32) as int32) as int32))) + -1) <= 0 by {
                    have (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((bound as int32) as int32) as int32))) + (let integer_constant: Integer = -1; integer_constant)) <= (0 + 0) by {
                        apply(click::integer::add_le((to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((bound as int32) as int32) as int32)))), 0, (let integer_constant: Integer = -1; integer_constant), 0)) using {
                            (to_integer((((value as int32) as int32) as int32)) + (-1 *
                                to_integer((((bound as int32) as int32) as int32)))) <= 0;
                            (let integer_constant: Integer = -1; integer_constant) <= 0;
                            defined(((value - 1) as int32));
                            defined((value - 1));
                            defined(old(((value - 1) as int32)));
                            defined(old((value - 1)));
                        };
                    }
                    have (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((bound as int32) as int32) as int32))) + -1) == (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((bound as int32) as int32) as int32))) + (let integer_constant: Integer = -1; integer_constant)) by {
                        normalize();
                    }
                    have (let integer_value: Integer = 0; integer_value) == (0 + 0) by {
                        normalize();
                    }
                    apply(click::integer::le_substitute((to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((bound as int32) as int32) as int32))) + (let integer_constant: Integer = -1; integer_constant)), (0 + 0), (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((bound as int32) as int32) as int32))) + -1), 0)) using {
                        (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((bound
                            as int32) as int32) as int32))) + (let integer_constant: Integer = -1;
                            integer_constant)) <= (0 + 0);
                        (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((bound
                            as int32) as int32) as int32))) + -1) == (to_integer((((value as int32) as
                            int32) as int32)) + (-1 * to_integer((((bound as int32) as int32) as
                            int32))) + (let integer_constant: Integer = -1; integer_constant));
                        (let integer_value: Integer = 0; integer_value) == (0 + 0);
                        defined(((value - 1) as int32));
                        defined((value - 1));
                        defined(old(((value - 1) as int32)));
                        defined(old((value - 1)));
                    };
                }
                have (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((bound as int32) as int32) as int32))) + -1) == ((to_integer(((value as int32) as int32)) + -1) - (to_integer(((bound as int32) as int32)) + 0)) by {
                    normalize();
                }
                apply(click::integer::difference_le((to_integer(((value as int32) as int32)) + -1), (to_integer(((bound as int32) as int32)) + 0), (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((bound as int32) as int32) as int32))) + -1))) using {
                    (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((bound as
                        int32) as int32) as int32))) + -1) <= 0;
                    (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((bound as
                        int32) as int32) as int32))) + -1) == ((to_integer(((value as int32) as int32))
                        + -1) - (to_integer(((bound as int32) as int32)) + 0));
                    defined(((value - 1) as int32));
                    defined((value - 1));
                    defined(old(((value - 1) as int32)));
                    defined(old((value - 1)));
                };
            }
            normalize() using {
                (to_integer(((value as int32) as int32)) + -1) <= (to_integer(((bound as int32) as
                    int32)) + 0);
            };
        }
        have ((value - 1) as int32) <= (bound as int32) by {
            have defined(((value - 1) as int32)) by {
                known();
            }
            have defined((value - 1)) by {
                known();
            }
            have defined(old(((value - 1) as int32))) by {
                known();
            }
            have defined(old((value - 1))) by {
                known();
            }
            have to_integer((((value - 1) as int32) as int32)) <= to_integer(((bound as int32) as int32)) by {
                have (to_integer(((value as int32) as int32)) + -1 + (-1 * (to_integer(((bound as int32) as int32)) + 0))) <= 0 by {
                    have (to_integer(((value as int32) as int32)) + -1 + (-1 * (to_integer(((bound as int32) as int32)) + 0))) == ((to_integer(((value as int32) as int32)) + -1) - (to_integer(((bound as int32) as int32)) + 0)) by {
                        normalize();
                    }
                    apply(click::integer::le_difference((to_integer(((value as int32) as int32)) + -1), (to_integer(((bound as int32) as int32)) + 0), (to_integer(((value as int32) as int32)) + -1 + (-1 * (to_integer(((bound as int32) as int32)) + 0))))) using {
                        (to_integer(((value as int32) as int32)) + -1) <= (to_integer(((bound as int32)
                            as int32)) + 0);
                        (to_integer(((value as int32) as int32)) + -1 + (-1 * (to_integer(((bound as
                            int32) as int32)) + 0))) == ((to_integer(((value as int32) as int32)) + -1)
                            - (to_integer(((bound as int32) as int32)) + 0));
                        defined(((value - 1) as int32));
                        defined((value - 1));
                        defined(old(((value - 1) as int32)));
                        defined(old((value - 1)));
                    };
                }
                have ((-1 * (to_integer((value as int32)) - to_integer((1 as int32)))) + to_integer(((value - 1) as int32))) == 0 by {
                    have (to_integer(((value - 1) as int32)) - (to_integer((value as int32)) - to_integer((1 as int32)))) == 0 by {
                        apply(click::integer::equal_difference(to_integer(((value - 1) as int32)), (to_integer((value as int32)) - to_integer((1 as int32))))) using {
                            to_integer(((value - 1) as int32)) == (to_integer((value as int32)) -
                                to_integer((1 as int32)));
                            defined(((value - 1) as int32));
                            defined((value - 1));
                            defined(old(((value - 1) as int32)));
                            defined(old((value - 1)));
                        };
                    }
                    have ((-1 * (to_integer((value as int32)) - to_integer((1 as int32)))) + to_integer(((value - 1) as int32))) == (to_integer(((value - 1) as int32)) - (to_integer((value as int32)) - to_integer((1 as int32)))) by {
                        normalize();
                    }
                    apply(click::integer::equal_substitute((to_integer(((value - 1) as int32)) - (to_integer((value as int32)) - to_integer((1 as int32)))), 0, ((-1 * (to_integer((value as int32)) - to_integer((1 as int32)))) + to_integer(((value - 1) as int32))), 0)) using {
                        (to_integer(((value - 1) as int32)) - (to_integer((value as int32)) -
                            to_integer((1 as int32)))) == 0;
                        ((-1 * (to_integer((value as int32)) - to_integer((1 as int32)))) +
                            to_integer(((value - 1) as int32))) == (to_integer(((value - 1) as int32)) -
                            (to_integer((value as int32)) - to_integer((1 as int32))));
                        (let integer_value: Integer = 0; integer_value) == 0;
                        defined(((value - 1) as int32));
                        defined((value - 1));
                        defined(old(((value - 1) as int32)));
                        defined(old((value - 1)));
                    };
                }
                have ((-1 * (to_integer((value as int32)) - to_integer((1 as int32)))) + to_integer(((value - 1) as int32))) <= 0 by {
                    apply(click::integer::equal_le(((-1 * (to_integer((value as int32)) - to_integer((1 as int32)))) + to_integer(((value - 1) as int32))), 0)) using {
                        ((-1 * (to_integer((value as int32)) - to_integer((1 as int32)))) +
                            to_integer(((value - 1) as int32))) == 0;
                        defined(((value - 1) as int32));
                        defined((value - 1));
                        defined(old(((value - 1) as int32)));
                        defined(old((value - 1)));
                    };
                }
                have ((-1 * (to_integer((value as int32)) - to_integer((1 as int32)))) + to_integer(((value - 1) as int32)) + (to_integer(((value as int32) as int32)) + -1) + (-1 * (to_integer(((bound as int32) as int32)) + 0))) <= 0 by {
                    have (to_integer(((value as int32) as int32)) + -1 + (-1 * (to_integer(((bound as int32) as int32)) + 0)) + ((-1 * (to_integer((value as int32)) - to_integer((1 as int32)))) + to_integer(((value - 1) as int32)))) <= (0 + 0) by {
                        apply(click::integer::add_le((to_integer(((value as int32) as int32)) + -1 + (-1 * (to_integer(((bound as int32) as int32)) + 0))), 0, ((-1 * (to_integer((value as int32)) - to_integer((1 as int32)))) + to_integer(((value - 1) as int32))), 0)) using {
                            (to_integer(((value as int32) as int32)) + -1 + (-1 * (to_integer(((bound as
                                int32) as int32)) + 0))) <= 0;
                            ((-1 * (to_integer((value as int32)) - to_integer((1 as int32)))) +
                                to_integer(((value - 1) as int32))) <= 0;
                            defined(((value - 1) as int32));
                            defined((value - 1));
                            defined(old(((value - 1) as int32)));
                            defined(old((value - 1)));
                        };
                    }
                    have ((-1 * (to_integer((value as int32)) - to_integer((1 as int32)))) + to_integer(((value - 1) as int32)) + (to_integer(((value as int32) as int32)) + -1) + (-1 * (to_integer(((bound as int32) as int32)) + 0))) == (to_integer(((value as int32) as int32)) + -1 + (-1 * (to_integer(((bound as int32) as int32)) + 0)) + ((-1 * (to_integer((value as int32)) - to_integer((1 as int32)))) + to_integer(((value - 1) as int32)))) by {
                        normalize();
                    }
                    have (let integer_value: Integer = 0; integer_value) == (0 + 0) by {
                        normalize();
                    }
                    apply(click::integer::le_substitute((to_integer(((value as int32) as int32)) + -1 + (-1 * (to_integer(((bound as int32) as int32)) + 0)) + ((-1 * (to_integer((value as int32)) - to_integer((1 as int32)))) + to_integer(((value - 1) as int32)))), (0 + 0), ((-1 * (to_integer((value as int32)) - to_integer((1 as int32)))) + to_integer(((value - 1) as int32)) + (to_integer(((value as int32) as int32)) + -1) + (-1 * (to_integer(((bound as int32) as int32)) + 0))), 0)) using {
                        (to_integer(((value as int32) as int32)) + -1 + (-1 * (to_integer(((bound as
                            int32) as int32)) + 0)) + ((-1 * (to_integer((value as int32)) -
                            to_integer((1 as int32)))) + to_integer(((value - 1) as int32)))) <= (0 +
                            0);
                        ((-1 * (to_integer((value as int32)) - to_integer((1 as int32)))) +
                            to_integer(((value - 1) as int32)) + (to_integer(((value as int32) as
                            int32)) + -1) + (-1 * (to_integer(((bound as int32) as int32)) + 0))) ==
                            (to_integer(((value as int32) as int32)) + -1 + (-1 * (to_integer(((bound as
                            int32) as int32)) + 0)) + ((-1 * (to_integer((value as int32)) -
                            to_integer((1 as int32)))) + to_integer(((value - 1) as int32))));
                        (let integer_value: Integer = 0; integer_value) == (0 + 0);
                        defined(((value - 1) as int32));
                        defined((value - 1));
                        defined(old(((value - 1) as int32)));
                        defined(old((value - 1)));
                    };
                }
                have ((-1 * (to_integer((value as int32)) - to_integer((1 as int32)))) + to_integer(((value - 1) as int32)) + (to_integer(((value as int32) as int32)) + -1) + (-1 * (to_integer(((bound as int32) as int32)) + 0))) == (to_integer((((value - 1) as int32) as int32)) - to_integer(((bound as int32) as int32))) by {
                    normalize();
                }
                apply(click::integer::difference_le(to_integer((((value - 1) as int32) as int32)), to_integer(((bound as int32) as int32)), ((-1 * (to_integer((value as int32)) - to_integer((1 as int32)))) + to_integer(((value - 1) as int32)) + (to_integer(((value as int32) as int32)) + -1) + (-1 * (to_integer(((bound as int32) as int32)) + 0))))) using {
                    ((-1 * (to_integer((value as int32)) - to_integer((1 as int32)))) +
                        to_integer(((value - 1) as int32)) + (to_integer(((value as int32) as int32)) +
                        -1) + (-1 * (to_integer(((bound as int32) as int32)) + 0))) <= 0;
                    ((-1 * (to_integer((value as int32)) - to_integer((1 as int32)))) +
                        to_integer(((value - 1) as int32)) + (to_integer(((value as int32) as int32)) +
                        -1) + (-1 * (to_integer(((bound as int32) as int32)) + 0))) ==
                        (to_integer((((value - 1) as int32) as int32)) - to_integer(((bound as int32) as
                        int32)));
                    defined(((value - 1) as int32));
                    defined((value - 1));
                    defined(old(((value - 1) as int32)));
                    defined(old((value - 1)));
                };
            }
            normalize() using {
                to_integer((((value - 1) as int32) as int32)) <= to_integer(((bound as int32) as
                    int32));
            };
        }
        have to_integer((value - 1)) <= to_integer(bound) by {
            normalize() using {
                ((value - 1) as int32) <= (bound as int32);
                to_integer(((value - 1) as int32)) == (to_integer((value as int32)) - to_integer((1 as
                    int32)));
            };
        }
        known();
    }
}

theorem int32_less_equal_and_not_less_than_implies_equal(left: int32, right: int32) {
    requires left <= right;
    requires not (left < right);

    ensures left == right by {
        have to_integer((left as int32)) == to_integer((right as int32)) by {
            have ((-1 * to_integer((right as int32))) + to_integer((left as int32))) <= 0 by {
                have to_integer((left as int32)) <= to_integer((right as int32)) by {
                    normalize() using {
                        left <= right;
                    };
                }
                have ((-1 * to_integer((right as int32))) + to_integer((left as int32))) == (to_integer((left as int32)) - to_integer((right as int32))) by {
                    normalize();
                }
                apply(integer::le_difference(to_integer((left as int32)), to_integer((right as int32)), ((-1 * to_integer((right as int32))) + to_integer((left as int32))))) using {
                    to_integer((left as int32)) <= to_integer((right as int32));
                    ((-1 * to_integer((right as int32))) + to_integer((left as int32))) ==
                        (to_integer((left as int32)) - to_integer((right as int32)));
                };
            }
            have (to_integer((right as int32)) + (-1 * to_integer((left as int32)))) <= 0 by {
                have to_integer((right as int32)) <= to_integer((left as int32)) by {
                    normalize() using {
                        not left < right;
                    };
                }
                have (to_integer((right as int32)) + (-1 * to_integer((left as int32)))) == (to_integer((right as int32)) - to_integer((left as int32))) by {
                    normalize();
                }
                apply(integer::le_difference(to_integer((right as int32)), to_integer((left as int32)), (to_integer((right as int32)) + (-1 * to_integer((left as int32)))))) using {
                    to_integer((right as int32)) <= to_integer((left as int32));
                    (to_integer((right as int32)) + (-1 * to_integer((left as int32)))) ==
                        (to_integer((right as int32)) - to_integer((left as int32)));
                };
            }
            have ((-1 * to_integer((right as int32))) + to_integer((left as int32))) == 0 by {
                have ((-1 * to_integer((right as int32))) + to_integer((left as int32))) <= ((-1 * to_integer((right as int32))) + to_integer((left as int32))) by {
                    normalize();
                }
                have (to_integer((right as int32)) + (-1 * to_integer((left as int32))) + ((-1 * to_integer((right as int32))) + to_integer((left as int32)))) <= (0 + ((-1 * to_integer((right as int32))) + to_integer((left as int32)))) by {
                    apply(integer::add_le((to_integer((right as int32)) + (-1 * to_integer((left as int32)))), 0, ((-1 * to_integer((right as int32))) + to_integer((left as int32))), ((-1 * to_integer((right as int32))) + to_integer((left as int32))))) using {
                        (to_integer((right as int32)) + (-1 * to_integer((left as int32)))) <= 0;
                        ((-1 * to_integer((right as int32))) + to_integer((left as int32))) <= ((-1 *
                            to_integer((right as int32))) + to_integer((left as int32)));
                    };
                }
                have 0 <= ((-1 * to_integer((right as int32))) + to_integer((left as int32))) by {
                    have 0 == (to_integer((right as int32)) + (-1 * to_integer((left as int32))) + ((-1 * to_integer((right as int32))) + to_integer((left as int32)))) by {
                        normalize();
                    }
                    have ((-1 * to_integer((right as int32))) + to_integer((left as int32))) == (0 + ((-1 * to_integer((right as int32))) + to_integer((left as int32)))) by {
                        normalize();
                    }
                    apply(integer::le_substitute((to_integer((right as int32)) + (-1 * to_integer((left as int32))) + ((-1 * to_integer((right as int32))) + to_integer((left as int32)))), (0 + ((-1 * to_integer((right as int32))) + to_integer((left as int32)))), 0, ((-1 * to_integer((right as int32))) + to_integer((left as int32))))) using {
                        (to_integer((right as int32)) + (-1 * to_integer((left as int32))) + ((-1 *
                            to_integer((right as int32))) + to_integer((left as int32)))) <= (0 + ((-1 *
                            to_integer((right as int32))) + to_integer((left as int32))));
                        0 == (to_integer((right as int32)) + (-1 * to_integer((left as int32))) + ((-1 *
                            to_integer((right as int32))) + to_integer((left as int32))));
                        ((-1 * to_integer((right as int32))) + to_integer((left as int32))) == (0 + ((-1
                            * to_integer((right as int32))) + to_integer((left as int32))));
                    };
                }
                apply(integer::le_antisymmetric(((-1 * to_integer((right as int32))) + to_integer((left as int32))), 0)) using {
                    ((-1 * to_integer((right as int32))) + to_integer((left as int32))) <= 0;
                    0 <= ((-1 * to_integer((right as int32))) + to_integer((left as int32)));
                };
            }
            have ((-1 * to_integer((right as int32))) + to_integer((left as int32)) + to_integer((right as int32))) == (0 + to_integer((right as int32))) by {
                apply(integer::equal_add(((-1 * to_integer((right as int32))) + to_integer((left as int32))), 0, to_integer((right as int32)), to_integer((right as int32)))) using {
                    ((-1 * to_integer((right as int32))) + to_integer((left as int32))) == 0;
                    to_integer((right as int32)) == to_integer((right as int32));
                };
            }
            have to_integer((left as int32)) == ((-1 * to_integer((right as int32))) + to_integer((left as int32)) + to_integer((right as int32))) by {
                normalize();
            }
            have to_integer((right as int32)) == (0 + to_integer((right as int32))) by {
                normalize();
            }
            apply(integer::equal_substitute(((-1 * to_integer((right as int32))) + to_integer((left as int32)) + to_integer((right as int32))), (0 + to_integer((right as int32))), to_integer((left as int32)), to_integer((right as int32)))) using {
                ((-1 * to_integer((right as int32))) + to_integer((left as int32)) + to_integer((right
                    as int32))) == (0 + to_integer((right as int32)));
                to_integer((left as int32)) == ((-1 * to_integer((right as int32))) + to_integer((left
                    as int32)) + to_integer((right as int32)));
                to_integer((right as int32)) == (0 + to_integer((right as int32)));
            };
        }
        normalize() using {
            to_integer((left as int32)) == to_integer((right as int32));
        };
    }
}

theorem int32_less_equal_and_not_equal_implies_less_than(left: int32, right: int32) {
    requires left <= right;
    requires left != right;

    ensures left < right by {
        have to_integer(((left as int32) as int32)) < to_integer(((right as int32) as int32)) by {
            have not not to_integer(((left as int32) as int32)) < to_integer(((right as int32) as int32)) by {
                intro();
                have ((-1 * to_integer(((left as int32) as int32))) + to_integer(((right as int32) as int32))) <= 0 by {
                    have to_integer(((right as int32) as int32)) <= to_integer(((left as int32) as int32)) by {
                        normalize() using {
                            not to_integer(((left as int32) as int32)) < to_integer(((right as int32) as
                                int32));
                        };
                    }
                    have ((-1 * to_integer(((left as int32) as int32))) + to_integer(((right as int32) as int32))) == (to_integer(((right as int32) as int32)) - to_integer(((left as int32) as int32))) by {
                        normalize();
                    }
                    apply(click::integer::le_difference(to_integer(((right as int32) as int32)), to_integer(((left as int32) as int32)), ((-1 * to_integer(((left as int32) as int32))) + to_integer(((right as int32) as int32))))) using {
                        to_integer(((right as int32) as int32)) <= to_integer(((left as int32) as
                            int32));
                        ((-1 * to_integer(((left as int32) as int32))) + to_integer(((right as int32) as
                            int32))) == (to_integer(((right as int32) as int32)) - to_integer(((left as
                            int32) as int32)));
                    };
                }
                have (to_integer(((left as int32) as int32)) + (-1 * to_integer(((right as int32) as int32)))) <= 0 by {
                    have to_integer((((left as int32) as int32) as int32)) <= to_integer((((right as int32) as int32) as int32)) by {
                        normalize() using {
                            ((left as int32) as int32) <= ((right as int32) as int32);
                        };
                    }
                    have (to_integer(((left as int32) as int32)) + (-1 * to_integer(((right as int32) as int32)))) == (to_integer((((left as int32) as int32) as int32)) - to_integer((((right as int32) as int32) as int32))) by {
                        normalize();
                    }
                    apply(click::integer::le_difference(to_integer((((left as int32) as int32) as int32)), to_integer((((right as int32) as int32) as int32)), (to_integer(((left as int32) as int32)) + (-1 * to_integer(((right as int32) as int32)))))) using {
                        to_integer((((left as int32) as int32) as int32)) <= to_integer((((right as
                            int32) as int32) as int32));
                        (to_integer(((left as int32) as int32)) + (-1 * to_integer(((right as int32) as
                            int32)))) == (to_integer((((left as int32) as int32) as int32)) -
                            to_integer((((right as int32) as int32) as int32)));
                    };
                }
                have (to_integer(((left as int32) as int32)) + (-1 * to_integer(((right as int32) as int32))) + 1) <= 0 by {
                    have to_integer((((left as int32) as int32) as int32)) <= to_integer((((right as int32) as int32) as int32)) by {
                        have (to_integer(((left as int32) as int32)) + (-1 * to_integer(((right as int32) as int32)))) == (to_integer((((left as int32) as int32) as int32)) - to_integer((((right as int32) as int32) as int32))) by {
                            normalize();
                        }
                        apply(click::integer::difference_le(to_integer((((left as int32) as int32) as int32)), to_integer((((right as int32) as int32) as int32)), (to_integer(((left as int32) as int32)) + (-1 * to_integer(((right as int32) as int32)))))) using {
                            (to_integer(((left as int32) as int32)) + (-1 * to_integer(((right as int32)
                                as int32)))) <= 0;
                            (to_integer(((left as int32) as int32)) + (-1 * to_integer(((right as int32)
                                as int32)))) == (to_integer((((left as int32) as int32) as int32)) -
                                to_integer((((right as int32) as int32) as int32)));
                        };
                    }
                    have to_integer((((left as int32) as int32) as int32)) != to_integer((((right as int32) as int32) as int32)) by {
                        normalize() using {
                            ((left as int32) as int32) != ((right as int32) as int32);
                        };
                    }
                    have to_integer((((left as int32) as int32) as int32)) < to_integer((((right as int32) as int32) as int32)) by {
                        apply(click::integer::le_ne_lt(to_integer((((left as int32) as int32) as int32)), to_integer((((right as int32) as int32) as int32)))) using {
                            to_integer((((left as int32) as int32) as int32)) <= to_integer((((right as
                                int32) as int32) as int32));
                            to_integer((((left as int32) as int32) as int32)) != to_integer((((right as
                                int32) as int32) as int32));
                        };
                    }
                    have (to_integer((((left as int32) as int32) as int32)) + 1) <= to_integer((((right as int32) as int32) as int32)) by {
                        apply(click::integer::lt_step_le(to_integer((((left as int32) as int32) as int32)), to_integer((((right as int32) as int32) as int32)))) using {
                            to_integer((((left as int32) as int32) as int32)) < to_integer((((right as
                                int32) as int32) as int32));
                        };
                    }
                    have (to_integer(((left as int32) as int32)) + (-1 * to_integer(((right as int32) as int32))) + 1) == ((to_integer((((left as int32) as int32) as int32)) + 1) - to_integer((((right as int32) as int32) as int32))) by {
                        normalize();
                    }
                    apply(click::integer::le_difference((to_integer((((left as int32) as int32) as int32)) + 1), to_integer((((right as int32) as int32) as int32)), (to_integer(((left as int32) as int32)) + (-1 * to_integer(((right as int32) as int32))) + 1))) using {
                        (to_integer((((left as int32) as int32) as int32)) + 1) <= to_integer((((right
                            as int32) as int32) as int32));
                        (to_integer(((left as int32) as int32)) + (-1 * to_integer(((right as int32) as
                            int32))) + 1) == ((to_integer((((left as int32) as int32) as int32)) + 1) -
                            to_integer((((right as int32) as int32) as int32)));
                    };
                }
                have (let integer_constant: Integer = 1; integer_constant) <= 0 by {
                    have ((-1 * to_integer(((left as int32) as int32))) + to_integer(((right as int32) as int32)) + (to_integer(((left as int32) as int32)) + (-1 * to_integer(((right as int32) as int32))) + 1)) <= (0 + 0) by {
                        apply(click::integer::add_le(((-1 * to_integer(((left as int32) as int32))) + to_integer(((right as int32) as int32))), 0, (to_integer(((left as int32) as int32)) + (-1 * to_integer(((right as int32) as int32))) + 1), 0)) using {
                            ((-1 * to_integer(((left as int32) as int32))) + to_integer(((right as
                                int32) as int32))) <= 0;
                            (to_integer(((left as int32) as int32)) + (-1 * to_integer(((right as int32)
                                as int32))) + 1) <= 0;
                        };
                    }
                    have (let integer_constant: Integer = 1; integer_constant) == ((-1 * to_integer(((left as int32) as int32))) + to_integer(((right as int32) as int32)) + (to_integer(((left as int32) as int32)) + (-1 * to_integer(((right as int32) as int32))) + 1)) by {
                        normalize();
                    }
                    have (let integer_value: Integer = 0; integer_value) == (0 + 0) by {
                        normalize();
                    }
                    apply(click::integer::le_substitute(((-1 * to_integer(((left as int32) as int32))) + to_integer(((right as int32) as int32)) + (to_integer(((left as int32) as int32)) + (-1 * to_integer(((right as int32) as int32))) + 1)), (0 + 0), (let integer_constant: Integer = 1; integer_constant), 0)) using {
                        ((-1 * to_integer(((left as int32) as int32))) + to_integer(((right as int32) as
                            int32)) + (to_integer(((left as int32) as int32)) + (-1 * to_integer(((right
                            as int32) as int32))) + 1)) <= (0 + 0);
                        (let integer_constant: Integer = 1; integer_constant) == ((-1 *
                            to_integer(((left as int32) as int32))) + to_integer(((right as int32) as
                            int32)) + (to_integer(((left as int32) as int32)) + (-1 * to_integer(((right
                            as int32) as int32))) + 1));
                        (let integer_value: Integer = 0; integer_value) == (0 + 0);
                    };
                }
                contradiction((let integer_constant: Integer = 1; integer_constant) <= 0);
            }
            normalize() using {
                not not to_integer(((left as int32) as int32)) < to_integer(((right as int32) as
                    int32));
            };
        }
        have left < right by {
            normalize() using {
                to_integer(((left as int32) as int32)) < to_integer(((right as int32) as int32));
            };
        }
        known();
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
            apply(integer::add_le(a, b, -a + -b, -a + -b)) using {
                a <= b; -a + -b <= -a + -b;
            };
        }
        have -b == a + (-a + -b) by { known(); }
        have -a == b + (-a + -b) by { known(); }
        rewrite(-b, a + (-a + -b));
        rewrite(-a, b + (-a + -b));
        known();
    }
}

theorem uint32_add_to_integer(left: uint32, right: uint32) {
    requires to_integer(left) + to_integer(right) <= 4294967295;
    ensures to_integer(left + right) == to_integer(left) + to_integer(right) by {
        have 0 <= to_integer(left) by known();
        have 0 <= to_integer(right) by known();
        have 0 + 0 <= (to_integer(left) + to_integer(right)) by {
            apply(integer::add_le(0, to_integer(left), 0, to_integer(right))) using { 0 <= to_integer(left); 0 <= to_integer(right); };
        }
        have 0 <= (to_integer(left) + to_integer(right)) by known();
        known();
    }
}

// Exact unsigned subtraction needs the native no-underflow guard.
theorem uint32_subtract_to_integer(left: uint32, right: uint32) {
    requires right <= left;
    ensures to_integer(left - right) == to_integer(left) - to_integer(right) by {
        have to_integer(right) <= to_integer(left) by known();
        have 0 <= to_integer(right) by known();
        have to_integer(left) <= 4294967295 by known();
        have to_integer(right) + -to_integer(right) <= (to_integer(left) + -to_integer(right)) by {
            apply(integer::add_le(to_integer(right), to_integer(left), -to_integer(right), -to_integer(right))) using { to_integer(right) <= to_integer(left); -to_integer(right) <= -to_integer(right); };
        }
        have 0 == to_integer(right) + -to_integer(right) by known();
        have (to_integer(left) - to_integer(right)) == (to_integer(left) + -to_integer(right)) by known();
        have 0 <= (to_integer(left) - to_integer(right)) by {
            apply(integer::le_substitute(to_integer(right) + -to_integer(right), (to_integer(left) + -to_integer(right)), 0, (to_integer(left) - to_integer(right)))) using { to_integer(right) + -to_integer(right) <= (to_integer(left) + -to_integer(right)); 0 == to_integer(right) + -to_integer(right); (to_integer(left) - to_integer(right)) == (to_integer(left) + -to_integer(right)); };
        }
        have -to_integer(right) <= 0 by {
            apply(integer::negate_order(0, to_integer(right))) using { 0 <= to_integer(right); };
            known();
        }
        have (to_integer(left) + -to_integer(right)) <= 4294967295 + 0 by {
            apply(integer::add_le(to_integer(left), 4294967295, -to_integer(right), 0)) using { to_integer(left) <= 4294967295; -to_integer(right) <= 0; };
        }
        have to_integer(4294967295u64) == 4294967295 + 0 by known();
        have (to_integer(left) - to_integer(right)) <= 4294967295 by {
            apply(integer::le_substitute((to_integer(left) + -to_integer(right)), 4294967295 + 0, (to_integer(left) - to_integer(right)), 4294967295)) using { (to_integer(left) + -to_integer(right)) <= 4294967295 + 0; (to_integer(left) - to_integer(right)) == (to_integer(left) + -to_integer(right)); to_integer(4294967295u64) == 4294967295 + 0; };
        }
        known();
    }
}

theorem uint64_add_to_integer(left: uint64, right: uint64) {
    requires to_integer(left) + to_integer(right) <= 18446744073709551615;
    ensures to_integer(left + right) == to_integer(left) + to_integer(right) by {
        have 0 <= to_integer(left) by known();
        have 0 <= to_integer(right) by known();
        have 0 + 0 <= (to_integer(left) + to_integer(right)) by {
            apply(integer::add_le(0, to_integer(left), 0, to_integer(right))) using { 0 <= to_integer(left); 0 <= to_integer(right); };
        }
        have 0 <= (to_integer(left) + to_integer(right)) by known();
        known();
    }
}

theorem uint64_multiply_to_integer(left: uint64, right: uint64) {
    requires to_integer(left) * to_integer(right) <= 18446744073709551615;
    ensures to_integer(left * right) == to_integer(left) * to_integer(right) by {
        have 0 <= to_integer(left) by known();
        have 0 <= to_integer(right) by known();
        have 0 * to_integer(right) <= (to_integer(left) * to_integer(right)) by {
            apply(integer::multiply_order_nonnegative(0, to_integer(left), to_integer(right))) using { 0 <= to_integer(left); 0 <= to_integer(right); };
        }
        have 0 <= (to_integer(left) * to_integer(right)) by known();
        known();
    }
}

theorem uint64_subtract_to_integer(left: uint64, right: uint64) {
    requires to_integer(right) <= to_integer(left);
    ensures to_integer(left - right) == to_integer(left) - to_integer(right) by {
        have to_integer(right) <= to_integer(left) by known();
        have 0 <= to_integer(right) by known();
        have to_integer(left) <= 18446744073709551615 by known();
        have to_integer(right) + -to_integer(right) <= (to_integer(left) + -to_integer(right)) by {
            apply(integer::add_le(to_integer(right), to_integer(left), -to_integer(right), -to_integer(right))) using { to_integer(right) <= to_integer(left); -to_integer(right) <= -to_integer(right); };
        }
        have 0 == to_integer(right) + -to_integer(right) by known();
        have (to_integer(left) - to_integer(right)) == (to_integer(left) + -to_integer(right)) by known();
        have 0 <= (to_integer(left) - to_integer(right)) by {
            apply(integer::le_substitute(to_integer(right) + -to_integer(right), (to_integer(left) + -to_integer(right)), 0, (to_integer(left) - to_integer(right)))) using { to_integer(right) + -to_integer(right) <= (to_integer(left) + -to_integer(right)); 0 == to_integer(right) + -to_integer(right); (to_integer(left) - to_integer(right)) == (to_integer(left) + -to_integer(right)); };
        }
        have -to_integer(right) <= 0 by {
            apply(integer::negate_order(0, to_integer(right))) using { 0 <= to_integer(right); };
            known();
        }
        have (to_integer(left) + -to_integer(right)) <= 18446744073709551615 + 0 by {
            apply(integer::add_le(to_integer(left), 18446744073709551615, -to_integer(right), 0)) using { to_integer(left) <= 18446744073709551615; -to_integer(right) <= 0; };
        }
        have to_integer(18446744073709551615u64) == 18446744073709551615 + 0 by known();
        have (to_integer(left) - to_integer(right)) <= 18446744073709551615 by {
            apply(integer::le_substitute((to_integer(left) + -to_integer(right)), 18446744073709551615 + 0, (to_integer(left) - to_integer(right)), 18446744073709551615)) using { (to_integer(left) + -to_integer(right)) <= 18446744073709551615 + 0; (to_integer(left) - to_integer(right)) == (to_integer(left) + -to_integer(right)); to_integer(18446744073709551615u64) == 18446744073709551615 + 0; };
        }
        known();
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
    ensures left <= right by known();
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
    ensures not (left >= right) by known();
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
    ensures to_integer(left) <= to_integer(right) by known();
}

theorem uint32_to_integer_less_equal_implies_less_equal(left: uint32, right: uint32) {
    requires to_integer(left) <= to_integer(right);
    ensures left <= right by known();
}

theorem uint32_to_integer_equal_implies_equal(left: uint32, right: uint32) {
    requires to_integer(left) == to_integer(right);
    ensures left == right by known();
}

theorem uint32_to_integer_bounds(value: uint32) {
    ensures 0 <= to_integer(value) by {
        have 0u32 <= value;
        apply(integer::uint32_less_equal_to_integer(0u32, value)) using { 0u32 <= value; };
    }
    ensures to_integer(value) <= 4294967295 by {
        have value <= 4294967295u32;
        apply(integer::uint32_less_equal_to_integer(value, 4294967295u32)) using { value <= 4294967295u32; };
    }
}

theorem int32_add_to_integer(left: int32, right: int32) {
    requires defined(left + right);
    ensures to_integer(left + right) == to_integer(left) + to_integer(right) by {
        have -2147483648 <= to_integer(left) + to_integer(right) by {
            known();
        }
        have to_integer(left) + to_integer(right) <= 2147483647 by {
            known();
        }
        have to_integer(left + right) == to_integer(left) + to_integer(right) by {
            known();
        }
        known();
    }
}

theorem int32_less_equal_to_integer(left: int32, right: int32) {
    requires left <= right;
    ensures to_integer(left) <= to_integer(right) by known();
}

theorem int32_to_integer_less_equal_implies_less_equal(left: int32, right: int32) {
    requires to_integer(left) <= to_integer(right);
    ensures left <= right by known();
}

theorem int64_to_integer_less_equal_implies_less_equal(left: int64, right: int64) {
    requires to_integer(left) <= to_integer(right);
    ensures left <= right by known();
}

theorem int32_subtract_to_integer(left: int32, right: int32) {
    requires defined(left - right);
    ensures to_integer(left - right) == to_integer(left) - to_integer(right) by {
        have -2147483648 <= to_integer(left) - to_integer(right) by {
            known();
        }
        have to_integer(left) - to_integer(right) <= 2147483647 by {
            known();
        }
        have to_integer(left - right) == to_integer(left) - to_integer(right) by {
            known();
        }
        known();
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
        known();
    }
}

theorem to_int8_round_trip(z: Integer) {
    requires z >= -128;
    requires z <= 127;
    ensures to_integer(to_int8(z)) == z by {
        have -128 <= z by {
            known();
        }
        have z <= 127 by {
            known();
        }
        known();
    }
}

theorem to_int16_round_trip(z: Integer) {
    requires z >= -32768;
    requires z <= 32767;
    ensures to_integer(to_int16(z)) == z by {
        have -32768 <= z by {
            known();
        }
        have z <= 32767 by {
            known();
        }
        known();
    }
}

theorem to_int32_round_trip(z: Integer) {
    requires z >= -2147483648;
    requires z <= 2147483647;
    ensures to_integer(to_int32(z)) == z by {
        have -2147483648 <= z by {
            known();
        }
        have z <= 2147483647 by {
            known();
        }
        known();
    }
}

theorem to_uint8_round_trip(z: Integer) {
    requires z >= 0;
    requires z <= 255;
    ensures to_integer(to_uint8(z)) == z by {
        have 0 <= z by {
            known();
        }
        have z <= 255 by {
            known();
        }
        known();
    }
}

theorem to_uint16_round_trip(z: Integer) {
    requires z >= 0;
    requires z <= 65535;
    ensures to_integer(to_uint16(z)) == z by {
        have 0 <= z by {
            known();
        }
        have z <= 65535 by {
            known();
        }
        known();
    }
}

theorem to_uint32_round_trip(z: Integer) {
    requires z >= 0;
    requires z <= 4294967295;
    ensures to_integer(to_uint32(z)) == z by {
        have 0 <= z by {
            known();
        }
        have z <= 4294967295 by {
            known();
        }
        known();
    }
}

theorem to_int64_round_trip(z: Integer) {
    requires z >= -9223372036854775808;
    requires z <= 9223372036854775807;
    ensures to_integer(to_int64(z)) == z by {
        have -9223372036854775808 <= z by {
            known();
        }
        have z <= 9223372036854775807 by {
            known();
        }
        known();
    }
}

theorem to_uint64_round_trip(z: Integer) {
    requires z >= 0;
    requires z <= 18446744073709551615;
    ensures to_integer(to_uint64(z)) == z by {
        have 0 <= z by {
            known();
        }
        have z <= 18446744073709551615 by {
            known();
        }
        known();
    }
}

theorem int64_subtract_to_integer(left: int64, right: int64) {
    requires defined(left - right);
    ensures to_integer(left - right) == to_integer(left) - to_integer(right) by {
        have -9223372036854775808 <= to_integer(left) - to_integer(right) by {
            known();
        }
        have to_integer(left) - to_integer(right) <= 9223372036854775807 by {
            known();
        }
        have to_integer(left - right) == to_integer(left) - to_integer(right) by {
            known();
        }
        known();
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
            solve() using { n == q * d + r; 1 - d <= r; };
        } else {
            have 0 <= r by { solve() using { not (r < 0); }; }
            have value == q;
            rewrite(value, q);
            solve() using { n == q * d + r; 0 <= r; };
        }
    }
    ensures n < (value + 1) * d by {
        if r < 0 {
            have value == q + -1;
            have value + 1 == q by { solve() using { value == q + -1; }; }
            rewrite(value + 1, q);
            solve() using { n == q * d + r; r < 0; };
        } else {
            have 0 <= r by { solve() using { not (r < 0); }; }
            have value == q;
            apply(integer::multiply_add(q, 1, d));
            rewrite(value, q);
            rewrite((q + 1) * d, q * d + 1 * d);
            solve() using { n == q * d + r; r <= d - 1; };
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
            solve() using { n == q * d + r; r <= d - 1; };
        } else {
            have r <= 0 by { solve() using { not (0 < r); }; }
            have value == q;
            rewrite(value, q);
            solve() using { n == q * d + r; r <= 0; };
        }
    }
    ensures (value + -1) * d < n by {
        if 0 < r {
            have value == q + 1;
            have value + -1 == q by { solve() using { value == q + 1; }; }
            rewrite(value + -1, q);
            solve() using { n == q * d + r; 0 < r; };
        } else {
            have r <= 0 by { solve() using { not (0 < r); }; }
            have value == q;
            apply(integer::multiply_add(q, -1, d));
            rewrite(value, q);
            rewrite((q + -1) * d, q * d + -1 * d);
            solve() using { n == q * d + r; 1 - d <= r; };
        }
    }
}



theorem le_transitive(a: Integer, b: Integer, c: Integer) {
    requires a <= b;
    requires b <= c;
    ensures a <= c by {
        have a + b <= b + c by {
            apply(integer::add_le(a, b, b, c)) using { a <= b; b <= c; };
        }
        have (a + b) + -b <= (b + c) + -b by {
            apply(integer::add_le(a + b, b + c, -b, -b)) using {
                a + b <= b + c; -b <= -b;
            };
        }
        have a == (a + b) + -b by { known(); }
        have c == (b + c) + -b by { known(); }
        rewrite(a, (a + b) + -b);
        rewrite(c, (b + c) + -b);
        known();
    }
}

theorem uint64_increment_upper_bound(value: uint64, upper: uint64) {
    requires value < upper;
    ensures to_integer(value + 1u64) <= to_integer(upper) by {
        have to_integer(value) < to_integer(upper) by known();
        have (to_integer(value) + 1) <= to_integer(upper) by {
            apply(integer::lt_step_le(to_integer(value), to_integer(upper))) using {
                to_integer(value) < to_integer(upper);
            };
        }
        have to_integer(upper) <= 18446744073709551615 by known();
        have (to_integer(value) + 1) <= 18446744073709551615 by {
            apply(integer::le_transitive(to_integer(value) + 1, to_integer(upper), 18446744073709551615)) using {
                to_integer(value) + 1 <= to_integer(upper);
                to_integer(upper) <= 18446744073709551615;
            };
        }
        have (to_integer(value) + to_integer(1u64)) <= 18446744073709551615 by known();
        have to_integer(value + 1u64) == (to_integer(value) + 1) by {
            apply(integer::uint64_add_to_integer(value, 1u64)) using {
                to_integer(value) + to_integer(1u64) <= 18446744073709551615;
            };
            known();
        }
        rewrite(to_integer(value + 1u64), to_integer(value) + 1);
        known();
    }
}

theorem lt_le(a: Integer, b: Integer) {
    requires a < b;
    ensures a <= b by {
        have a + 1 <= b by {
            apply(integer::lt_step_le(a, b)) using { a < b; };
        }
        have a <= a + 1 by { known(); }
        apply(integer::le_transitive(a, a + 1, b)) using { a <= a + 1; a + 1 <= b; };
    }
}

theorem add_right_order(a: Integer, b: Integer, c: Integer) {
    requires a <= b;
    ensures a + c <= b + c by {
        apply(integer::add_le(a, b, c, c)) using { a <= b; c <= c; };
    }
}

theorem int32_less_equal_less_than_transitive(first: int32, middle: int32, last: int32) {
    requires first <= middle;
    requires middle < last;

    ensures first < last by {
        have (to_integer(first) + 1) <= (to_integer(middle) + 1) by {
            apply(integer::add_right_order(to_integer(first), to_integer(middle), 1)) using {
                to_integer(first) <= to_integer(middle);
            };
        }
        have (to_integer(middle) + 1) <= to_integer(last) by {
            apply(integer::lt_step_le(to_integer(middle), to_integer(last))) using {
                to_integer(middle) < to_integer(last);
            };
        }
        have (to_integer(first) + 1) <= to_integer(last) by {
            apply(integer::le_transitive(to_integer(first) + 1, to_integer(middle) + 1, to_integer(last))) using {
                (to_integer(first) + 1) <= (to_integer(middle) + 1);
                (to_integer(middle) + 1) <= to_integer(last);
            };
        }
        apply(integer::step_le_lt(to_integer(first), to_integer(last))) using {
            (to_integer(first) + 1) <= to_integer(last);
        };
        known();
    }
}

theorem int32_less_equal_transitive(first: int32, middle: int32, last: int32) {
    requires first <= middle;
    requires middle <= last;

    ensures first <= last by {
        apply(integer::le_transitive(to_integer(first), to_integer(middle), to_integer(last))) using {
            to_integer(first) <= to_integer(middle);
            to_integer(middle) <= to_integer(last);
        };
        known();
    }
}

theorem uint64_less_than_less_equal_transitive(first: uint64, middle: uint64, last: uint64) {
    requires first < middle;
    requires middle <= last;

    ensures first < last by {
        have (to_integer(first) + 1) <= to_integer(middle) by {
            apply(integer::lt_step_le(to_integer(first), to_integer(middle))) using {
                to_integer(first) < to_integer(middle);
            };
        }
        have (to_integer(first) + 1) <= to_integer(last) by {
            apply(integer::le_transitive(to_integer(first) + 1, to_integer(middle), to_integer(last))) using {
                (to_integer(first) + 1) <= to_integer(middle);
                to_integer(middle) <= to_integer(last);
            };
        }
        apply(integer::step_le_lt(to_integer(first), to_integer(last))) using {
            (to_integer(first) + 1) <= to_integer(last);
        };
        known();
    }
}

theorem uint64_less_equal_transitive(first: uint64, middle: uint64, last: uint64) {
    requires first <= middle;
    requires middle <= last;

    ensures first <= last by {
        apply(integer::le_transitive(to_integer(first), to_integer(middle), to_integer(last))) using {
            to_integer(first) <= to_integer(middle);
            to_integer(middle) <= to_integer(last);
        };
        known();
    }
}

theorem subtract_right_order(a: Integer, b: Integer, c: Integer) {
    requires a <= b;
    ensures a - c <= b - c by {
        have a + -c <= b + -c by {
            apply(integer::add_right_order(a, b, -c)) using { a <= b; };
        }
        have a - c == a + -c by {
            known();
        }
        have b - c == b + -c by {
            known();
        }
        apply(integer::le_substitute(a + -c, b + -c, a - c, b - c)) using { a + -c <= b + -c; a - c == a + -c; b - c == b + -c; };
    }
}

theorem lt_le_predecessor(a: Integer, b: Integer) {
    requires a < b;
    ensures a <= b - 1 by {
        have a + 1 <= b by {
            apply(integer::lt_step_le(a, b)) using { a < b; };
        }
        have (a + 1) - 1 <= b - 1 by {
            apply(integer::subtract_right_order(a + 1, b, 1)) using { a + 1 <= b; };
        }
        have a == (a + 1) - 1 by { known(); }
        rewrite(a, (a + 1) - 1);
        known();
    }
}

theorem subtract_left_order(a: Integer, b: Integer, c: Integer) {
    requires a <= b;
    ensures c - b <= c - a by {
        have -b <= -a by {
            apply(integer::negate_order(a, b)) using { a <= b; };
        }
        have -b + c <= -a + c by {
            apply(integer::add_right_order(-b, -a, c)) using { -b <= -a; };
        }
        have c - b == -b + c by {
            known();
        }
        have c - a == -a + c by {
            known();
        }
        apply(integer::le_substitute(-b + c, -a + c, c - b, c - a)) using { -b + c <= -a + c; c - b == -b + c; c - a == -a + c; };
    }
}

theorem subtract_le(a: Integer, b: Integer, c: Integer, d: Integer) {
    requires a <= b;
    requires d <= c;
    ensures a - c <= b - d by {
        have a - c <= b - c by {
            apply(integer::subtract_right_order(a, b, c)) using { a <= b; };
        }
        have b - c <= b - d by {
            apply(integer::subtract_left_order(d, c, b)) using { d <= c; };
        }
        apply(integer::le_transitive(a - c, b - c, b - d)) using {
            a - c <= b - c;
            b - c <= b - d;
        };
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
        known();
    }
}

theorem sum_commute(a: Integer, b: Integer, c: Integer) {
    requires a == b + c;
    ensures a == c + b by {
        have c + b == b + c by {
            known();
        }
        rewrite(c + b, b + c);
        known();
    }
}

theorem sum_difference(a: Integer, b: Integer, c: Integer) {
    requires a == b + c;
    ensures a + -c == b by {
        have a + -c == (b + c) + -c by {
            apply(integer::equal_add(a, b + c, -c, -c)) using { a == b + c; -c == -c; };
        }
        have b == (b + c) + -c by {
            known();
        }
        rewrite(b, (b + c) + -c);
        known();
    }
    ensures -b == -a + c by {
        have a + -c == b by {
            have a + -c == (b + c) + -c by {
                apply(integer::equal_add(a, b + c, -c, -c)) using { a == b + c; -c == -c; };
            }
            have b == (b + c) + -c by {
                known();
            }
            rewrite(b, (b + c) + -c);
            known();
        }
        have -(a + -c) == -b by {
            apply(integer::equal_negate(a + -c, b)) using { a + -c == b; };
        }
        have -a + c == -(a + -c) by {
            known();
        }
        rewrite(-a + c, -(a + -c));
        known();
    }
}

theorem positive_divisor_quotient_lower(n: Integer, d: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires (bound * d) <= n;
    ensures bound <= truncating_quotient(n, d) by {
        have 0 < d by {
            have 0 + 1 <= d by {
                known();
            }
            apply(integer::step_le_lt(0, d)) using { 0 + 1 <= d; };
        }
        have n == (truncating_quotient(n, d) * d) + truncating_remainder(n, d) by {
            apply(integer::truncation_identity(n, d)) using { d != 0; };
        }
        have n + -(truncating_remainder(n, d)) == (truncating_quotient(n, d) * d) by {
            apply(integer::sum_difference(n, (truncating_quotient(n, d) * d), truncating_remainder(n, d))) using { n == (truncating_quotient(n, d) * d) + truncating_remainder(n, d); d != 0; };
        }
        have -(truncating_quotient(n, d) * d) == -n + truncating_remainder(n, d) by {
            apply(integer::sum_difference(n, (truncating_quotient(n, d) * d), truncating_remainder(n, d))) using { n == (truncating_quotient(n, d) * d) + truncating_remainder(n, d); d != 0; };
        }
        have n == truncating_remainder(n, d) + (truncating_quotient(n, d) * d) by {
            apply(integer::sum_commute(n, (truncating_quotient(n, d) * d), truncating_remainder(n, d))) using { n == (truncating_quotient(n, d) * d) + truncating_remainder(n, d); d != 0; };
        }
        have truncating_remainder(n, d) <= (d - 1) by {
            apply(integer::positive_divisor_remainder_upper(n, d)) using { d != 0; 0 < d; };
        }
        have -(d - 1) <= -(truncating_remainder(n, d)) by {
            apply(integer::negate_order(truncating_remainder(n, d), (d - 1))) using { truncating_remainder(n, d) <= (d - 1); d != 0; };
        }
        have (bound * d) + -(d - 1) <= n + -(truncating_remainder(n, d)) by {
            apply(integer::add_le((bound * d), n, -(d - 1), -(truncating_remainder(n, d)))) using { (bound * d) <= n; -(d - 1) <= -(truncating_remainder(n, d)); d != 0; };
        }
        have (bound * d) - (d - 1) <= (truncating_quotient(n, d) * d) by {
            have (bound * d) - (d - 1) == (bound * d) + -(d - 1) by {
                known();
            }
            have (truncating_quotient(n, d) * d) == n + -(truncating_remainder(n, d)) by {
                known();
            }
            apply(integer::le_substitute((bound * d) + -(d - 1), n + -(truncating_remainder(n, d)), (bound * d) - (d - 1), (truncating_quotient(n, d) * d))) using { (bound * d) + -(d - 1) <= n + -(truncating_remainder(n, d)); (bound * d) - (d - 1) == (bound * d) + -(d - 1); (truncating_quotient(n, d) * d) == n + -(truncating_remainder(n, d)); d != 0; };
        }
        have -(truncating_quotient(n, d) * d) <= -((bound * d) - (d - 1)) by {
            apply(integer::negate_order((bound * d) - (d - 1), (truncating_quotient(n, d) * d))) using { (bound * d) - (d - 1) <= (truncating_quotient(n, d) * d); d != 0; };
        }
        have -(truncating_quotient(n, d)) * d == -(truncating_quotient(n, d) * d) by {
            apply(integer::negate_multiply(truncating_quotient(n, d), d)) using { d != 0; };
        }
        have -bound * d == -(bound * d) by {
            apply(integer::negate_multiply(bound, d));
        }
        have -(truncating_quotient(n, d)) * d <= -bound * d + (d - 1) by {
            have -(truncating_quotient(n, d)) * d == -(truncating_quotient(n, d) * d) by {
                rewrite(-(truncating_quotient(n, d)) * d, -(truncating_quotient(n, d) * d));
                known();
            }
            have -bound * d + (d - 1) == -((bound * d) - (d - 1)) by {
                rewrite(-bound * d, -(bound * d));
                known();
            }
            apply(integer::le_substitute(-(truncating_quotient(n, d) * d), -((bound * d) - (d - 1)), -(truncating_quotient(n, d)) * d, -bound * d + (d - 1))) using { -(truncating_quotient(n, d) * d) <= -((bound * d) - (d - 1)); -(truncating_quotient(n, d)) * d == -(truncating_quotient(n, d) * d); -bound * d + (d - 1) == -((bound * d) - (d - 1)); d != 0; };
        }
        have 0 < d by {
            have 0 + 1 <= d by {
                known();
            }
            apply(integer::step_le_lt(0, d)) using { 0 + 1 <= d; };
        }
        have (d - 1) < d by {
            known();
        }
        have -(truncating_quotient(n, d)) <= -bound by {
            apply(integer::round_down_le(-(truncating_quotient(n, d)), -bound, d, (d - 1))) using { 0 < d; (d - 1) < d; -(truncating_quotient(n, d)) * d <= -bound * d + (d - 1); d != 0; };
        }
        have -(-bound) <= -(-(truncating_quotient(n, d))) by {
            apply(integer::negate_order(-(truncating_quotient(n, d)), -bound)) using { -(truncating_quotient(n, d)) <= -bound; d != 0; };
        }
        have bound == -(-bound) by {
            known();
        }
        have truncating_quotient(n, d) == -(-(truncating_quotient(n, d))) by {
            known();
        }
        apply(integer::le_substitute(-(-bound), -(-(truncating_quotient(n, d))), bound, truncating_quotient(n, d))) using { -(-bound) <= -(-(truncating_quotient(n, d))); bound == -(-bound); truncating_quotient(n, d) == -(-(truncating_quotient(n, d))); d != 0; };
    }
}

theorem positive_divisor_quotient_upper(n: Integer, d: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires n <= (bound * d);
    ensures truncating_quotient(n, d) <= bound by {
        have 0 < d by {
            have 0 + 1 <= d by {
                known();
            }
            apply(integer::step_le_lt(0, d)) using { 0 + 1 <= d; };
        }
        have n == (truncating_quotient(n, d) * d) + truncating_remainder(n, d) by {
            apply(integer::truncation_identity(n, d)) using { d != 0; };
        }
        have n + -(truncating_remainder(n, d)) == (truncating_quotient(n, d) * d) by {
            apply(integer::sum_difference(n, (truncating_quotient(n, d) * d), truncating_remainder(n, d))) using { n == (truncating_quotient(n, d) * d) + truncating_remainder(n, d); d != 0; };
        }
        have -(truncating_quotient(n, d) * d) == -n + truncating_remainder(n, d) by {
            apply(integer::sum_difference(n, (truncating_quotient(n, d) * d), truncating_remainder(n, d))) using { n == (truncating_quotient(n, d) * d) + truncating_remainder(n, d); d != 0; };
        }
        have n == truncating_remainder(n, d) + (truncating_quotient(n, d) * d) by {
            apply(integer::sum_commute(n, (truncating_quotient(n, d) * d), truncating_remainder(n, d))) using { n == (truncating_quotient(n, d) * d) + truncating_remainder(n, d); d != 0; };
        }
        have 1 - d <= truncating_remainder(n, d) by {
            apply(integer::positive_divisor_remainder_lower(n, d)) using { d != 0; 0 < d; };
        }
        have -(truncating_remainder(n, d)) <= (d - 1) by {
            have -(truncating_remainder(n, d)) <= -(1 - d) by {
                apply(integer::negate_order(1 - d, truncating_remainder(n, d))) using { 1 - d <= truncating_remainder(n, d); d != 0; };
            }
            have -(truncating_remainder(n, d)) == -(truncating_remainder(n, d)) by {
                known();
            }
            have (d - 1) == -(1 - d) by {
                known();
            }
            apply(integer::le_substitute(-(truncating_remainder(n, d)), -(1 - d), -(truncating_remainder(n, d)), (d - 1))) using { -(truncating_remainder(n, d)) <= -(1 - d); -(truncating_remainder(n, d)) == -(truncating_remainder(n, d)); (d - 1) == -(1 - d); d != 0; };
        }
        have n + -(truncating_remainder(n, d)) <= (bound * d) + (d - 1) by {
            apply(integer::add_le(n, (bound * d), -(truncating_remainder(n, d)), (d - 1))) using { n <= (bound * d); -(truncating_remainder(n, d)) <= (d - 1); d != 0; };
        }
        have (truncating_quotient(n, d) * d) <= (bound * d) + (d - 1) by {
            have (truncating_quotient(n, d) * d) == n + -(truncating_remainder(n, d)) by {
                known();
            }
            have (bound * d) + (d - 1) == (bound * d) + (d - 1) by {
                known();
            }
            apply(integer::le_substitute(n + -(truncating_remainder(n, d)), (bound * d) + (d - 1), (truncating_quotient(n, d) * d), (bound * d) + (d - 1))) using { n + -(truncating_remainder(n, d)) <= (bound * d) + (d - 1); (truncating_quotient(n, d) * d) == n + -(truncating_remainder(n, d)); (bound * d) + (d - 1) == (bound * d) + (d - 1); d != 0; };
        }
        have 0 < d by {
            have 0 + 1 <= d by {
                known();
            }
            apply(integer::step_le_lt(0, d)) using { 0 + 1 <= d; };
        }
        have (d - 1) < d by {
            known();
        }
        apply(integer::round_down_le(truncating_quotient(n, d), bound, d, (d - 1))) using { 0 < d; (d - 1) < d; (truncating_quotient(n, d) * d) <= (bound * d) + (d - 1); d != 0; };
    }
}

theorem positive_divisor_quotient_strict_lower(n: Integer, d: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires bound < 0;
    requires bound * d < n;
    ensures bound < truncating_quotient(n, d) by {
        have bound * d <= n by { solve() using { bound * d < n; }; }
        apply(integer::positive_divisor_quotient_lower(n, d, bound));
        if bound < truncating_quotient(n, d) {
            known();
        } else {
            have truncating_quotient(n, d) == bound by { solve() using {
                bound <= truncating_quotient(n, d); not (bound < truncating_quotient(n, d));
            }; }
            if n <= 0 {
                have 0 < d by { solve() using { 1 <= d; }; }
                apply(integer::nonpositive_dividend_remainder(n, d));
                apply(integer::truncation_identity(n, d));
                have n == bound * d + truncating_remainder(n, d) by {
                    rewrite(bound, truncating_quotient(n, d));
                    known();
                }
                have not (bound * d < n) by { solve() using {
                    n == bound * d + truncating_remainder(n, d); truncating_remainder(n, d) <= 0;
                }; }
                contradiction(bound * d < n);
            } else {
                have 0 <= n by { solve() using { not (n <= 0); }; }
                have 0 * d <= n by { solve() using { 0 <= n; }; }
                apply(integer::positive_divisor_quotient_lower(n, d, 0));
                have not (bound < 0) by { solve() using {
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
        have n <= bound * d by { solve() using { n < bound * d; }; }
        apply(integer::positive_divisor_quotient_upper(n, d, bound));
        if truncating_quotient(n, d) < bound {
            known();
        } else {
            have truncating_quotient(n, d) == bound by { solve() using {
                truncating_quotient(n, d) <= bound; not (truncating_quotient(n, d) < bound);
            }; }
            if 0 <= n {
                have 0 < d by { solve() using { 1 <= d; }; }
                apply(integer::nonnegative_dividend_remainder(n, d));
                apply(integer::truncation_identity(n, d));
                have n == bound * d + truncating_remainder(n, d) by {
                    rewrite(bound, truncating_quotient(n, d));
                    known();
                }
                have not (n < bound * d) by { solve() using {
                    n == bound * d + truncating_remainder(n, d); 0 <= truncating_remainder(n, d);
                }; }
                contradiction(n < bound * d);
            } else {
                have n <= 0 by { solve() using { not (0 <= n); }; }
                have n <= 0 * d by { solve() using { n <= 0; }; }
                apply(integer::positive_divisor_quotient_upper(n, d, 0));
                have not (0 < bound) by { solve() using {
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
            known();
        } else {
            have q == lower by { solve() using { lower <= q; not (lower + 1 <= q); }; }
            have n == lower * d + r by {
                rewrite(lower, q);
                known();
            }
            have not (r < 0) by { solve() using { lower * d <= n; n == lower * d + r; }; }
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
            known();
        } else {
            have q == upper by { solve() using { q <= upper; not (q <= upper + -1); }; }
            have n == upper * d + r by {
                rewrite(upper, q);
                known();
            }
            have not (0 < r) by { solve() using { n <= upper * d; n == upper * d + r; }; }
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
                apply(integer::add_le(factor, 0, -factor, -factor)) using {
                    factor <= 0; -factor <= -factor;
                };
            }
            have 0 == factor + -factor by { known(); }
            have -factor == 0 + -factor by { known(); }
            rewrite(0, factor + -factor);
            rewrite(-factor, 0 + -factor);
            known();
        }
        have a * -factor <= b * -factor by {
            apply(integer::multiply_order_nonnegative(a, b, -factor)) using {
                a <= b; 0 <= -factor;
            };
        }
        have -(b * -factor) <= -(a * -factor) by {
            apply(integer::negate_order(a * -factor, b * -factor)) using {
                a * -factor <= b * -factor;
            };
        }
        have b * -factor == -(b * factor) by { apply(integer::multiply_negate(b, factor)); }
        have a * -factor == -(a * factor) by { apply(integer::multiply_negate(a, factor)); }
        have b * factor == -(-(b * factor)) by { known(); }
        have a * factor == -(-(a * factor)) by { known(); }
        rewrite(b * factor, -(-(b * factor)));
        rewrite(a * factor, -(-(a * factor)));
        rewrite(-(b * factor), b * -factor);
        rewrite(-(a * factor), a * -factor);
        known();
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
            apply(integer::multiply_order_nonnegative(lower, value, amount)) using { lower <= value; 0 <= amount; };
        }
        have size * lower <= amount * lower by {
            apply(integer::multiply_order_nonpositive(amount, size, lower)) using { amount <= size; lower <= 0; };
        }
        have lower * size == size * lower by { apply(integer::multiply_commutative(lower, size)); }
        have lower * amount == amount * lower by { apply(integer::multiply_commutative(lower, amount)); }
        have lower * size <= lower * amount by {
            rewrite(lower * size, size * lower);
            rewrite(lower * amount, amount * lower);
            known();
        }
        apply(integer::le_transitive(lower * size, lower * amount, value * amount)) using {
            lower * size <= lower * amount; lower * amount <= value * amount;
        };
    }
    ensures value * amount <= upper * size by {
        have value * amount <= upper * amount by {
            apply(integer::multiply_order_nonnegative(value, upper, amount)) using { value <= upper; 0 <= amount; };
        }
        have amount * upper <= size * upper by {
            apply(integer::multiply_order_nonnegative(amount, size, upper)) using { amount <= size; 0 <= upper; };
        }
        have upper * amount == amount * upper by { apply(integer::multiply_commutative(upper, amount)); }
        have upper * size == size * upper by { apply(integer::multiply_commutative(upper, size)); }
        have upper * amount <= upper * size by {
            rewrite(upper * amount, amount * upper);
            rewrite(upper * size, size * upper);
            known();
        }
        apply(integer::le_transitive(value * amount, upper * amount, upper * size)) using {
            value * amount <= upper * amount; upper * amount <= upper * size;
        };
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
                apply(integer::multiply_order_nonnegative(lo_y, y, x)) using { lo_y <= y; 0 <= x; };
            }
            if 0 <= lo_y {
                have lo_x * lo_y <= x * lo_y by {
                    apply(integer::multiply_order_nonnegative(lo_x, x, lo_y)) using { lo_x <= x; 0 <= lo_y; };
                }
                have x * lo_y == lo_y * x by { apply(integer::multiply_commutative(x, lo_y)); }
                have bound <= lo_y * x by {
                    rewrite(lo_y * x, x * lo_y);
                    apply(integer::le_transitive(bound, lo_x * lo_y, x * lo_y)) using { bound <= lo_x * lo_y; lo_x * lo_y <= x * lo_y; };
                }
                rewrite(x * y, y * x);
                apply(integer::le_transitive(bound, lo_y * x, y * x)) using { bound <= lo_y * x; lo_y * x <= y * x; };
            } else {
                have lo_y < 0 by { known(); }
                have lo_y <= 0 by {
                    apply(integer::lt_le(lo_y, 0)) using { lo_y < 0; };
                }
                have hi_x * lo_y <= x * lo_y by {
                    apply(integer::multiply_order_nonpositive(x, hi_x, lo_y)) using { x <= hi_x; lo_y <= 0; };
                }
                have x * lo_y == lo_y * x by { apply(integer::multiply_commutative(x, lo_y)); }
                have bound <= lo_y * x by {
                    rewrite(lo_y * x, x * lo_y);
                    apply(integer::le_transitive(bound, hi_x * lo_y, x * lo_y)) using { bound <= hi_x * lo_y; hi_x * lo_y <= x * lo_y; };
                }
                rewrite(x * y, y * x);
                apply(integer::le_transitive(bound, lo_y * x, y * x)) using { bound <= lo_y * x; lo_y * x <= y * x; };
            }
        } else {
            have x < 0 by { known(); }
                have x <= 0 by {
                    apply(integer::lt_le(x, 0)) using { x < 0; };
                }
            have hi_y * x <= y * x by {
                apply(integer::multiply_order_nonpositive(y, hi_y, x)) using { y <= hi_y; x <= 0; };
            }
            if 0 <= hi_y {
                have lo_x * hi_y <= x * hi_y by {
                    apply(integer::multiply_order_nonnegative(lo_x, x, hi_y)) using { lo_x <= x; 0 <= hi_y; };
                }
                have x * hi_y == hi_y * x by { apply(integer::multiply_commutative(x, hi_y)); }
                have bound <= hi_y * x by {
                    rewrite(hi_y * x, x * hi_y);
                    apply(integer::le_transitive(bound, lo_x * hi_y, x * hi_y)) using { bound <= lo_x * hi_y; lo_x * hi_y <= x * hi_y; };
                }
                rewrite(x * y, y * x);
                apply(integer::le_transitive(bound, hi_y * x, y * x)) using { bound <= hi_y * x; hi_y * x <= y * x; };
            } else {
                have hi_y < 0 by { known(); }
                have hi_y <= 0 by {
                    apply(integer::lt_le(hi_y, 0)) using { hi_y < 0; };
                }
                have hi_x * hi_y <= x * hi_y by {
                    apply(integer::multiply_order_nonpositive(x, hi_x, hi_y)) using { x <= hi_x; hi_y <= 0; };
                }
                have x * hi_y == hi_y * x by { apply(integer::multiply_commutative(x, hi_y)); }
                have bound <= hi_y * x by {
                    rewrite(hi_y * x, x * hi_y);
                    apply(integer::le_transitive(bound, hi_x * hi_y, x * hi_y)) using { bound <= hi_x * hi_y; hi_x * hi_y <= x * hi_y; };
                }
                rewrite(x * y, y * x);
                apply(integer::le_transitive(bound, hi_y * x, y * x)) using { bound <= hi_y * x; hi_y * x <= y * x; };
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
                apply(integer::multiply_order_nonnegative(y, hi_y, x)) using { y <= hi_y; 0 <= x; };
            }
            if 0 <= hi_y {
                have x * hi_y <= hi_x * hi_y by {
                    apply(integer::multiply_order_nonnegative(x, hi_x, hi_y)) using { x <= hi_x; 0 <= hi_y; };
                }
                have x * hi_y == hi_y * x by { apply(integer::multiply_commutative(x, hi_y)); }
                have hi_y * x <= bound by {
                    rewrite(hi_y * x, x * hi_y);
                    apply(integer::le_transitive(x * hi_y, hi_x * hi_y, bound)) using { x * hi_y <= hi_x * hi_y; hi_x * hi_y <= bound; };
                }
                rewrite(x * y, y * x);
                apply(integer::le_transitive(y * x, hi_y * x, bound)) using { y * x <= hi_y * x; hi_y * x <= bound; };
            } else {
                have hi_y < 0 by { known(); }
                have hi_y <= 0 by {
                    apply(integer::lt_le(hi_y, 0)) using { hi_y < 0; };
                }
                have x * hi_y <= lo_x * hi_y by {
                    apply(integer::multiply_order_nonpositive(lo_x, x, hi_y)) using { lo_x <= x; hi_y <= 0; };
                }
                have x * hi_y == hi_y * x by { apply(integer::multiply_commutative(x, hi_y)); }
                have hi_y * x <= bound by {
                    rewrite(hi_y * x, x * hi_y);
                    apply(integer::le_transitive(x * hi_y, lo_x * hi_y, bound)) using { x * hi_y <= lo_x * hi_y; lo_x * hi_y <= bound; };
                }
                rewrite(x * y, y * x);
                apply(integer::le_transitive(y * x, hi_y * x, bound)) using { y * x <= hi_y * x; hi_y * x <= bound; };
            }
        } else {
            have x < 0 by { known(); }
                have x <= 0 by {
                    apply(integer::lt_le(x, 0)) using { x < 0; };
                }
            have y * x <= lo_y * x by {
                apply(integer::multiply_order_nonpositive(lo_y, y, x)) using { lo_y <= y; x <= 0; };
            }
            if 0 <= lo_y {
                have x * lo_y <= hi_x * lo_y by {
                    apply(integer::multiply_order_nonnegative(x, hi_x, lo_y)) using { x <= hi_x; 0 <= lo_y; };
                }
                have x * lo_y == lo_y * x by { apply(integer::multiply_commutative(x, lo_y)); }
                have lo_y * x <= bound by {
                    rewrite(lo_y * x, x * lo_y);
                    apply(integer::le_transitive(x * lo_y, hi_x * lo_y, bound)) using { x * lo_y <= hi_x * lo_y; hi_x * lo_y <= bound; };
                }
                rewrite(x * y, y * x);
                apply(integer::le_transitive(y * x, lo_y * x, bound)) using { y * x <= lo_y * x; lo_y * x <= bound; };
            } else {
                have lo_y < 0 by { known(); }
                have lo_y <= 0 by {
                    apply(integer::lt_le(lo_y, 0)) using { lo_y < 0; };
                }
                have x * lo_y <= lo_x * lo_y by {
                    apply(integer::multiply_order_nonpositive(lo_x, x, lo_y)) using { lo_x <= x; lo_y <= 0; };
                }
                have x * lo_y == lo_y * x by { apply(integer::multiply_commutative(x, lo_y)); }
                have lo_y * x <= bound by {
                    rewrite(lo_y * x, x * lo_y);
                    apply(integer::le_transitive(x * lo_y, lo_x * lo_y, bound)) using { x * lo_y <= lo_x * lo_y; lo_x * lo_y <= bound; };
                }
                rewrite(x * y, y * x);
                apply(integer::le_transitive(y * x, lo_y * x, bound)) using { y * x <= lo_y * x; lo_y * x <= bound; };
            }
        }
    }
}

// Unsigned 32-bit product and remainder laws, proved from the division
// observations and the truncating-division lemmas above.
theorem uint32_multiply_to_integer(left: uint32, right: uint32) {
    requires right == 0u32 or left <= 4294967295u32 / right;
    ensures to_integer(left * right) == to_integer(left) * to_integer(right) by {
        have 0 <= to_integer(left) by known();
        have 0 <= to_integer(right) by known();
        have 0 * to_integer(right) <= (to_integer(left) * to_integer(right)) by {
            apply(integer::multiply_order_nonnegative(0, to_integer(left), to_integer(right))) using { 0 <= to_integer(left); 0 <= to_integer(right); };
        }
        have 0 <= (to_integer(left) * to_integer(right)) by known();
        if right == 0u32 {
            have to_integer(right) == 0 by known();
            have (to_integer(left) * to_integer(right)) == 0 by {
                rewrite(to_integer(right), 0);
                known();
            }
            have (to_integer(left) * to_integer(right)) <= 4294967295 by {
                apply(integer::le_substitute(0, 4294967295, (to_integer(left) * to_integer(right)), 4294967295)) using { 0 <= 4294967295; (to_integer(left) * to_integer(right)) == 0; 4294967295 == 4294967295; };
            }
            known();
        } else {
            have to_integer(right) != 0 by known();
            have to_integer(left) <= to_integer(4294967295u32 / right) by {
                cases {
                    right == 0u32 => { contradiction(right == 0u32); }
                    to_integer(left) <= to_integer(4294967295u32 / right) => { known(); }
                }
            }
            have to_integer(4294967295u32 / right) == truncating_quotient(4294967295, to_integer(right)) by {
                apply(integer::uint32_divide_to_integer(4294967295u32, right)) using { to_integer(right) != 0; };
            }
            have to_integer(left) <= truncating_quotient(4294967295, to_integer(right)) by {
                rewrite(truncating_quotient(4294967295, to_integer(right)), to_integer(4294967295u32 / right));
                known();
            }
            have 4294967295 == (truncating_quotient(4294967295, to_integer(right)) * to_integer(right)) + truncating_remainder(4294967295, to_integer(right)) by {
                apply(integer::truncation_identity(4294967295, to_integer(right))) using { to_integer(right) != 0; };
            }
            have 0 <= truncating_remainder(4294967295, to_integer(right)) by {
                apply(integer::nonnegative_dividend_remainder(4294967295, to_integer(right))) using { to_integer(right) != 0; 0 <= 4294967295; };
            }
            have (truncating_quotient(4294967295, to_integer(right)) * to_integer(right)) + 0 <= (truncating_quotient(4294967295, to_integer(right)) * to_integer(right)) + truncating_remainder(4294967295, to_integer(right)) by {
                apply(integer::add_le((truncating_quotient(4294967295, to_integer(right)) * to_integer(right)), (truncating_quotient(4294967295, to_integer(right)) * to_integer(right)), 0, truncating_remainder(4294967295, to_integer(right)))) using { (truncating_quotient(4294967295, to_integer(right)) * to_integer(right)) <= (truncating_quotient(4294967295, to_integer(right)) * to_integer(right)); 0 <= truncating_remainder(4294967295, to_integer(right)); to_integer(right) != 0; };
            }
            have (truncating_quotient(4294967295, to_integer(right)) * to_integer(right)) == (truncating_quotient(4294967295, to_integer(right)) * to_integer(right)) + 0 by known();
            have (truncating_quotient(4294967295, to_integer(right)) * to_integer(right)) <= 4294967295 by {
                apply(integer::le_substitute((truncating_quotient(4294967295, to_integer(right)) * to_integer(right)) + 0, (truncating_quotient(4294967295, to_integer(right)) * to_integer(right)) + truncating_remainder(4294967295, to_integer(right)), (truncating_quotient(4294967295, to_integer(right)) * to_integer(right)), 4294967295)) using { (truncating_quotient(4294967295, to_integer(right)) * to_integer(right)) + 0 <= (truncating_quotient(4294967295, to_integer(right)) * to_integer(right)) + truncating_remainder(4294967295, to_integer(right)); (truncating_quotient(4294967295, to_integer(right)) * to_integer(right)) == (truncating_quotient(4294967295, to_integer(right)) * to_integer(right)) + 0; 4294967295 == (truncating_quotient(4294967295, to_integer(right)) * to_integer(right)) + truncating_remainder(4294967295, to_integer(right)); to_integer(right) != 0; };
            }
            have (to_integer(left) * to_integer(right)) <= (truncating_quotient(4294967295, to_integer(right)) * to_integer(right)) by {
                apply(integer::multiply_order_nonnegative(to_integer(left), truncating_quotient(4294967295, to_integer(right)), to_integer(right))) using { to_integer(left) <= truncating_quotient(4294967295, to_integer(right)); 0 <= to_integer(right); to_integer(right) != 0; };
            }
            have (to_integer(left) * to_integer(right)) <= 4294967295 by {
                apply(integer::le_transitive((to_integer(left) * to_integer(right)), (truncating_quotient(4294967295, to_integer(right)) * to_integer(right)), 4294967295)) using { (to_integer(left) * to_integer(right)) <= (truncating_quotient(4294967295, to_integer(right)) * to_integer(right)); (truncating_quotient(4294967295, to_integer(right)) * to_integer(right)) <= 4294967295; to_integer(right) != 0; };
            }
            known();
        }
    }
}

theorem uint32_multiply_guard_by_integer_bound(left: uint32, right: uint32) {
    requires to_integer(left) * to_integer(right) <= 4294967295;
    ensures right == 0u32 or left <= 4294967295u32 / right by {
        if right == 0u32 {
            known();
        } else {
            have right != 0u32 by {
                normalize() using {
                    not right == 0u32;
                };
            }
            have 1 <= to_integer(right) by {
                have 1 <= to_integer(right) by {
                    have ((-1 * to_integer(right)) + 1) <= 0 by {
                        have (-1 * to_integer(right)) <= 0 by {
                            have 0 <= to_integer(right) by {
                                normalize();
                            }
                            have (-1 * to_integer(right)) == (0 - to_integer(right)) by {
                                normalize();
                            }
                            apply(integer::le_difference(0, to_integer(right), (-1 * to_integer(right)))) using {
                                0 <= to_integer(right);
                                (-1 * to_integer(right)) == (0 - to_integer(right));
                            };
                        }
                        have 0 <= to_integer(right) by {
                            have (-1 * to_integer(right)) == (0 - to_integer(right)) by {
                                normalize();
                            }
                            apply(integer::difference_le(0, to_integer(right), (-1 * to_integer(right)))) using {
                                (-1 * to_integer(right)) <= 0;
                                (-1 * to_integer(right)) == (0 - to_integer(right));
                            };
                        }
                        have 0 != to_integer(right) by {
                            normalize() using {
                                to_integer(right) != 0;
                            };
                        }
                        have 0 < to_integer(right) by {
                            apply(integer::le_ne_lt(0, to_integer(right))) using {
                                0 <= to_integer(right);
                                0 != to_integer(right);
                            };
                        }
                        have (0 + 1) <= to_integer(right) by {
                            apply(integer::lt_step_le(0, to_integer(right))) using {
                                0 < to_integer(right);
                            };
                        }
                        have ((-1 * to_integer(right)) + 1) == ((0 + 1) - to_integer(right)) by {
                            normalize();
                        }
                        apply(integer::le_difference((0 + 1), to_integer(right), ((-1 * to_integer(right)) + 1))) using {
                            (0 + 1) <= to_integer(right);
                            ((-1 * to_integer(right)) + 1) == ((0 + 1) - to_integer(right));
                        };
                    }
                    have ((-1 * to_integer(right)) + 1) == (1 - to_integer(right)) by {
                        normalize();
                    }
                    apply(integer::difference_le(1, to_integer(right), ((-1 * to_integer(right)) + 1))) using {
                        ((-1 * to_integer(right)) + 1) <= 0;
                        ((-1 * to_integer(right)) + 1) == (1 - to_integer(right));
                    };
                }
                normalize() using {
                    1 <= to_integer(right);
                };
            }
            apply(integer::positive_divisor_quotient_lower(4294967295, to_integer(right), to_integer(left))) using {
                to_integer(right) != 0;
                1 <= to_integer(right);
                (to_integer(left) * to_integer(right)) <= 4294967295;
            };
            apply(integer::uint32_divide_to_integer(4294967295u32, right)) using {
                right != 0u32;
                to_integer(right) != 0;
            };
            have to_integer(left) <= to_integer((4294967295u32 / right)) by {
                known();
            }
            have left <= (4294967295u32 / right) as uint32 by {
                normalize() using {
                    to_integer(left) <= to_integer((4294967295u32 / right));
                };
            }
            known();
        }
    }
}

theorem uint32_remainder_less_than_divisor(value: uint32, divisor: uint32) {
    requires divisor != 0u32;
    ensures value % divisor < divisor by {
        have to_integer(divisor) != 0 by normalize() using { divisor != 0u32; };
        have 0 <= to_integer(divisor) by normalize();
        have 0 < to_integer(divisor) by {
            apply(integer::le_ne_lt(0, to_integer(divisor))) using { 0 <= to_integer(divisor); 0 != to_integer(divisor); };
        }
        apply(integer::uint32_remainder_to_integer(value, divisor)) using { divisor != 0u32; to_integer(divisor) != 0; };
        apply(integer::positive_divisor_remainder_upper(to_integer(value), to_integer(divisor))) using { to_integer(divisor) != 0; 0 < to_integer(divisor); };
        have truncating_remainder(to_integer(value), to_integer(divisor)) + 1 <= (to_integer(divisor) - 1) + 1 by {
            apply(integer::add_le(truncating_remainder(to_integer(value), to_integer(divisor)), to_integer(divisor) - 1, 1, 1)) using { truncating_remainder(to_integer(value), to_integer(divisor)) <= to_integer(divisor) - 1; 1 <= 1; to_integer(divisor) != 0; };
        }
        have truncating_remainder(to_integer(value), to_integer(divisor)) + 1 <= to_integer(divisor) by {
            have to_integer(divisor) == (to_integer(divisor) - 1) + 1 by normalize();
            apply(integer::le_substitute(truncating_remainder(to_integer(value), to_integer(divisor)) + 1, (to_integer(divisor) - 1) + 1, truncating_remainder(to_integer(value), to_integer(divisor)) + 1, to_integer(divisor))) using {
                truncating_remainder(to_integer(value), to_integer(divisor)) + 1 <= (to_integer(divisor) - 1) + 1; truncating_remainder(to_integer(value), to_integer(divisor)) + 1 == truncating_remainder(to_integer(value), to_integer(divisor)) + 1; to_integer(divisor) == (to_integer(divisor) - 1) + 1; to_integer(divisor) != 0;
            };
        }
        have to_integer(value % divisor) + 1 == truncating_remainder(to_integer(value), to_integer(divisor)) + 1 by {
            apply(integer::equal_add(to_integer(value % divisor), truncating_remainder(to_integer(value), to_integer(divisor)), 1, 1)) using { to_integer(value % divisor) == truncating_remainder(to_integer(value), to_integer(divisor)); 1 == 1; divisor != 0u32; to_integer(divisor) != 0; };
        }
        have to_integer(value % divisor) + 1 <= to_integer(divisor) by {
            apply(integer::le_substitute(truncating_remainder(to_integer(value), to_integer(divisor)) + 1, to_integer(divisor), to_integer(value % divisor) + 1, to_integer(divisor))) using {
                truncating_remainder(to_integer(value), to_integer(divisor)) + 1 <= to_integer(divisor); to_integer(value % divisor) + 1 == truncating_remainder(to_integer(value), to_integer(divisor)) + 1; to_integer(divisor) == to_integer(divisor); divisor != 0u32; to_integer(divisor) != 0;
            };
        }
        apply(integer::step_le_lt(to_integer(value % divisor), to_integer(divisor))) using { to_integer(value % divisor) + 1 <= to_integer(divisor); divisor != 0u32; to_integer(divisor) != 0; };
    }
}

theorem uint32_less_than_divisor_implies_remainder_is_value(value: uint32, divisor: uint32) {
    requires value < divisor;
    ensures value % divisor == value by {
        have to_integer(value) < to_integer(divisor) by {
            normalize() using {
                value < divisor;
            };
        }
        have 0 <= to_integer(value) by {
            normalize();
        }
        have 1 <= to_integer(divisor) by {
            have 1 <= to_integer(divisor) by {
                have (to_integer(value) + (-1 * to_integer(divisor)) + 1) <= 0 by {
                    have (to_integer(value) + 1) <= to_integer(divisor) by {
                        apply(integer::lt_step_le(to_integer(value), to_integer(divisor))) using {
                            to_integer(value) < to_integer(divisor);
                        };
                    }
                    have (to_integer(value) + (-1 * to_integer(divisor)) + 1) == ((to_integer(value) + 1) - to_integer(divisor)) by {
                        normalize();
                    }
                    apply(integer::le_difference((to_integer(value) + 1), to_integer(divisor), (to_integer(value) + (-1 * to_integer(divisor)) + 1))) using {
                        (to_integer(value) + 1) <= to_integer(divisor);
                        (to_integer(value) + (-1 * to_integer(divisor)) + 1) == ((to_integer(value) + 1)
                            - to_integer(divisor));
                    };
                }
                have (-1 * to_integer(value)) <= 0 by {
                    have 0 <= to_integer(value) by {
                        normalize();
                    }
                    have (-1 * to_integer(value)) == (0 - to_integer(value)) by {
                        normalize();
                    }
                    apply(integer::le_difference(0, to_integer(value), (-1 * to_integer(value)))) using {
                        0 <= to_integer(value);
                        (-1 * to_integer(value)) == (0 - to_integer(value));
                    };
                }
                have ((-1 * to_integer(divisor)) + 1) <= 0 by {
                    have (to_integer(value) + (-1 * to_integer(divisor)) + 1 + (-1 * to_integer(value))) <= (0 + 0) by {
                        apply(integer::add_le((to_integer(value) + (-1 * to_integer(divisor)) + 1), 0, (-1 * to_integer(value)), 0)) using {
                            (to_integer(value) + (-1 * to_integer(divisor)) + 1) <= 0;
                            (-1 * to_integer(value)) <= 0;
                        };
                    }
                    have ((-1 * to_integer(divisor)) + 1) == (to_integer(value) + (-1 * to_integer(divisor)) + 1 + (-1 * to_integer(value))) by {
                        normalize();
                    }
                    have (let integer_value: Integer = 0; integer_value) == (0 + 0) by {
                        normalize();
                    }
                    apply(integer::le_substitute((to_integer(value) + (-1 * to_integer(divisor)) + 1 + (-1 * to_integer(value))), (0 + 0), ((-1 * to_integer(divisor)) + 1), 0)) using {
                        (to_integer(value) + (-1 * to_integer(divisor)) + 1 + (-1 * to_integer(value)))
                            <= (0 + 0);
                        ((-1 * to_integer(divisor)) + 1) == (to_integer(value) + (-1 *
                            to_integer(divisor)) + 1 + (-1 * to_integer(value)));
                        (let integer_value: Integer = 0; integer_value) == (0 + 0);
                    };
                }
                have ((-1 * to_integer(divisor)) + 1) == (1 - to_integer(divisor)) by {
                    normalize();
                }
                apply(integer::difference_le(1, to_integer(divisor), ((-1 * to_integer(divisor)) + 1))) using {
                    ((-1 * to_integer(divisor)) + 1) <= 0;
                    ((-1 * to_integer(divisor)) + 1) == (1 - to_integer(divisor));
                };
            }
            normalize() using {
                1 <= to_integer(divisor);
            };
        }
        have to_integer(divisor) != 0 by {
            normalize() using {
                1 <= to_integer(divisor);
            };
        }
        have divisor != 0u32 by {
            normalize() using {
                to_integer(divisor) != 0;
            };
        }
        apply(integer::uint32_remainder_to_integer(value, divisor)) using {
            divisor != 0u32;
            to_integer(divisor) != 0;
        };
        have (0 * to_integer(divisor)) <= to_integer(value) by {
            have (0 * to_integer(divisor)) <= to_integer(value) by {
                have (-1 * to_integer(value)) <= 0 by {
                    have (-1 * to_integer(value)) == (0 - to_integer(value)) by {
                        normalize();
                    }
                    apply(integer::le_difference(0, to_integer(value), (-1 * to_integer(value)))) using {
                        0 <= to_integer(value);
                        (-1 * to_integer(value)) == (0 - to_integer(value));
                    };
                }
                have (-1 * to_integer(value)) == ((0 * to_integer(divisor)) - to_integer(value)) by {
                    normalize();
                }
                apply(integer::difference_le((0 * to_integer(divisor)), to_integer(value), (-1 * to_integer(value)))) using {
                    (-1 * to_integer(value)) <= 0;
                    (-1 * to_integer(value)) == ((0 * to_integer(divisor)) - to_integer(value));
                };
            }
            normalize() using {
                (0 * to_integer(divisor)) <= to_integer(value);
            };
        }
        apply(integer::positive_divisor_quotient_lower(to_integer(value), to_integer(divisor), 0)) using {
            to_integer(divisor) != 0;
            1 <= to_integer(divisor);
            (0 * to_integer(divisor)) <= to_integer(value);
        };
        have to_integer(value) < (1 * to_integer(divisor)) by {
            have to_integer(value) < (1 * to_integer(divisor)) by {
                have (to_integer(value) + (-1 * to_integer(divisor)) + 1) <= 0 by {
                    have (to_integer(value) + 1) <= to_integer(divisor) by {
                        apply(integer::lt_step_le(to_integer(value), to_integer(divisor))) using {
                            to_integer(value) < to_integer(divisor);
                        };
                    }
                    have (to_integer(value) + (-1 * to_integer(divisor)) + 1) == ((to_integer(value) + 1) - to_integer(divisor)) by {
                        normalize();
                    }
                    apply(integer::le_difference((to_integer(value) + 1), to_integer(divisor), (to_integer(value) + (-1 * to_integer(divisor)) + 1))) using {
                        (to_integer(value) + 1) <= to_integer(divisor);
                        (to_integer(value) + (-1 * to_integer(divisor)) + 1) == ((to_integer(value) + 1)
                            - to_integer(divisor));
                    };
                }
                have (to_integer(value) + (-1 * to_integer(divisor)) + 1) == ((to_integer(value) + 1) - (1 * to_integer(divisor))) by {
                    normalize();
                }
                apply(integer::difference_le((to_integer(value) + 1), (1 * to_integer(divisor)), (to_integer(value) + (-1 * to_integer(divisor)) + 1))) using {
                    (to_integer(value) + (-1 * to_integer(divisor)) + 1) <= 0;
                    (to_integer(value) + (-1 * to_integer(divisor)) + 1) == ((to_integer(value) + 1) -
                        (1 * to_integer(divisor)));
                };
                apply(integer::step_le_lt(to_integer(value), (1 * to_integer(divisor)))) using {
                    (to_integer(value) + 1) <= (1 * to_integer(divisor));
                };
            }
            normalize() using {
                to_integer(value) < (1 * to_integer(divisor));
            };
        }
        have 0 < 1 by {
            normalize();
        }
        apply(integer::positive_divisor_quotient_strict_upper(to_integer(value), to_integer(divisor), 1)) using {
            to_integer(divisor) != 0;
            1 <= to_integer(divisor);
            0 < 1;
            to_integer(value) < (1 * to_integer(divisor));
        };
        have truncating_quotient(to_integer(value), to_integer(divisor)) == 0 by {
            have truncating_quotient(to_integer(value), to_integer(divisor)) + 1 <= 1 by {
                apply(integer::lt_step_le(truncating_quotient(to_integer(value), to_integer(divisor)), 1)) using { truncating_quotient(to_integer(value), to_integer(divisor)) < 1; to_integer(divisor) != 0; };
            }
            have truncating_quotient(to_integer(value), to_integer(divisor)) <= 0 by {
                have truncating_quotient(to_integer(value), to_integer(divisor)) == (truncating_quotient(to_integer(value), to_integer(divisor)) + 1) - 1 by normalize();
                apply(integer::le_difference(truncating_quotient(to_integer(value), to_integer(divisor)) + 1, 1, truncating_quotient(to_integer(value), to_integer(divisor)))) using { truncating_quotient(to_integer(value), to_integer(divisor)) + 1 <= 1; truncating_quotient(to_integer(value), to_integer(divisor)) == (truncating_quotient(to_integer(value), to_integer(divisor)) + 1) - 1; to_integer(divisor) != 0; };
            }
            apply(integer::le_antisymmetric(truncating_quotient(to_integer(value), to_integer(divisor)), 0)) using { truncating_quotient(to_integer(value), to_integer(divisor)) <= 0; 0 <= truncating_quotient(to_integer(value), to_integer(divisor)); to_integer(divisor) != 0; };
        }
        apply(integer::truncation_identity(to_integer(value), to_integer(divisor))) using {
            to_integer(divisor) != 0;
        };
        have (truncating_quotient(to_integer(value), to_integer(divisor)) * to_integer(divisor)) == 0 by {
            rewrite(truncating_quotient(to_integer(value), to_integer(divisor)), 0);
            normalize();
        }
        have to_integer((value % divisor)) == to_integer(value) by {
            have (truncating_quotient(to_integer(value), to_integer(divisor)) * to_integer(divisor)) + truncating_remainder(to_integer(value), to_integer(divisor)) == 0 + truncating_remainder(to_integer(value), to_integer(divisor)) by {
                apply(integer::equal_add((truncating_quotient(to_integer(value), to_integer(divisor)) * to_integer(divisor)), 0, truncating_remainder(to_integer(value), to_integer(divisor)), truncating_remainder(to_integer(value), to_integer(divisor)))) using { (truncating_quotient(to_integer(value), to_integer(divisor)) * to_integer(divisor)) == 0; truncating_remainder(to_integer(value), to_integer(divisor)) == truncating_remainder(to_integer(value), to_integer(divisor)); to_integer(divisor) != 0; };
            }
            have truncating_remainder(to_integer(value), to_integer(divisor)) == 0 + truncating_remainder(to_integer(value), to_integer(divisor)) by normalize();
            have (truncating_quotient(to_integer(value), to_integer(divisor)) * to_integer(divisor)) + truncating_remainder(to_integer(value), to_integer(divisor)) == truncating_remainder(to_integer(value), to_integer(divisor)) by {
                apply(integer::equal_substitute((truncating_quotient(to_integer(value), to_integer(divisor)) * to_integer(divisor)) + truncating_remainder(to_integer(value), to_integer(divisor)), 0 + truncating_remainder(to_integer(value), to_integer(divisor)), (truncating_quotient(to_integer(value), to_integer(divisor)) * to_integer(divisor)) + truncating_remainder(to_integer(value), to_integer(divisor)), truncating_remainder(to_integer(value), to_integer(divisor)))) using {
                    (truncating_quotient(to_integer(value), to_integer(divisor)) * to_integer(divisor)) + truncating_remainder(to_integer(value), to_integer(divisor)) == 0 + truncating_remainder(to_integer(value), to_integer(divisor)); (truncating_quotient(to_integer(value), to_integer(divisor)) * to_integer(divisor)) + truncating_remainder(to_integer(value), to_integer(divisor)) == (truncating_quotient(to_integer(value), to_integer(divisor)) * to_integer(divisor)) + truncating_remainder(to_integer(value), to_integer(divisor)); truncating_remainder(to_integer(value), to_integer(divisor)) == 0 + truncating_remainder(to_integer(value), to_integer(divisor)); to_integer(divisor) != 0;
                };
            }
            have to_integer(value) == truncating_remainder(to_integer(value), to_integer(divisor)) by {
                apply(integer::equal_substitute((truncating_quotient(to_integer(value), to_integer(divisor)) * to_integer(divisor)) + truncating_remainder(to_integer(value), to_integer(divisor)), truncating_remainder(to_integer(value), to_integer(divisor)), to_integer(value), truncating_remainder(to_integer(value), to_integer(divisor)))) using {
                    (truncating_quotient(to_integer(value), to_integer(divisor)) * to_integer(divisor)) + truncating_remainder(to_integer(value), to_integer(divisor)) == truncating_remainder(to_integer(value), to_integer(divisor)); to_integer(value) == (truncating_quotient(to_integer(value), to_integer(divisor)) * to_integer(divisor)) + truncating_remainder(to_integer(value), to_integer(divisor)); truncating_remainder(to_integer(value), to_integer(divisor)) == truncating_remainder(to_integer(value), to_integer(divisor)); to_integer(divisor) != 0;
                };
            }
            apply(integer::equal_substitute(truncating_remainder(to_integer(value), to_integer(divisor)), truncating_remainder(to_integer(value), to_integer(divisor)), to_integer(value % divisor), to_integer(value))) using {
                truncating_remainder(to_integer(value), to_integer(divisor)) == truncating_remainder(to_integer(value), to_integer(divisor)); to_integer(value % divisor) == truncating_remainder(to_integer(value), to_integer(divisor)); to_integer(value) == truncating_remainder(to_integer(value), to_integer(divisor)); divisor != 0u32; to_integer(divisor) != 0;
            };
        }
        known();
    }
}

// A native nonzero quotient guard bounds the exact Integer product.
theorem uint64_product_bound_from_division(x: uint64, y: uint64) {
    requires y != 0u64;
    requires x <= 18446744073709551615u64 / y;
    ensures to_integer(x) * to_integer(y) <= to_integer(18446744073709551615u64) by {
        have to_integer(y) != 0;
        have 0 <= to_integer(y);
        have 0 <= to_integer(18446744073709551615u64) by normalize();
        apply(integer::uint64_divide_to_integer(18446744073709551615u64, y)) using {
            y != 0u64;
            to_integer(y) != 0;
        };
        have to_integer(x) <= to_integer(18446744073709551615u64 / y);
        apply(integer::multiply_order_nonnegative(to_integer(x), to_integer(18446744073709551615u64 / y), to_integer(y))) using {
            to_integer(x) <= to_integer(18446744073709551615u64 / y);
            0 <= to_integer(y);
            y != 0u64;
        };
        apply(integer::truncation_identity(to_integer(18446744073709551615u64), to_integer(y))) using { to_integer(y) != 0; };
        apply(integer::nonnegative_dividend_remainder(to_integer(18446744073709551615u64), to_integer(y))) using {
            to_integer(y) != 0;
            0 <= to_integer(18446744073709551615u64);
        };
        have to_integer(18446744073709551615u64 / y) * to_integer(y) == truncating_quotient(to_integer(18446744073709551615u64), to_integer(y)) * to_integer(y) by {
            rewrite(to_integer(18446744073709551615u64 / y), truncating_quotient(to_integer(18446744073709551615u64), to_integer(y)));
            normalize();
        }
        solve() using {
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
            apply(integer::truncation_identity(n, d)) using { d != 0; };
        }
        have n + -(truncating_remainder(n, d)) == (truncating_quotient(n, d) * d) by {
            apply(integer::sum_difference(n, (truncating_quotient(n, d) * d), truncating_remainder(n, d))) using { n == (truncating_quotient(n, d) * d) + truncating_remainder(n, d); d != 0; };
        }
        have -(truncating_quotient(n, d) * d) == -n + truncating_remainder(n, d) by {
            apply(integer::sum_difference(n, (truncating_quotient(n, d) * d), truncating_remainder(n, d))) using { n == (truncating_quotient(n, d) * d) + truncating_remainder(n, d); d != 0; };
        }
        have n == truncating_remainder(n, d) + (truncating_quotient(n, d) * d) by {
            apply(integer::sum_commute(n, (truncating_quotient(n, d) * d), truncating_remainder(n, d))) using { n == (truncating_quotient(n, d) * d) + truncating_remainder(n, d); d != 0; };
        }
        have 0 <= truncating_remainder(n, d) by {
            apply(integer::nonnegative_dividend_remainder(n, d)) using { d != 0; 0 <= n; };
        }
        have 0 + (truncating_quotient(n, d) * d) <= truncating_remainder(n, d) + (truncating_quotient(n, d) * d) by {
            apply(integer::add_le(0, truncating_remainder(n, d), (truncating_quotient(n, d) * d), (truncating_quotient(n, d) * d))) using { 0 <= truncating_remainder(n, d); (truncating_quotient(n, d) * d) <= (truncating_quotient(n, d) * d); d != 0; };
        }
        have (truncating_quotient(n, d) * d) <= n by {
            have (truncating_quotient(n, d) * d) == 0 + (truncating_quotient(n, d) * d) by {
                known();
            }
            have n == truncating_remainder(n, d) + (truncating_quotient(n, d) * d) by {
                known();
            }
            apply(integer::le_substitute(0 + (truncating_quotient(n, d) * d), truncating_remainder(n, d) + (truncating_quotient(n, d) * d), (truncating_quotient(n, d) * d), n)) using { 0 + (truncating_quotient(n, d) * d) <= truncating_remainder(n, d) + (truncating_quotient(n, d) * d); (truncating_quotient(n, d) * d) == 0 + (truncating_quotient(n, d) * d); n == truncating_remainder(n, d) + (truncating_quotient(n, d) * d); d != 0; };
        }
        have (truncating_quotient(n, d) * d) <= (bound * d) + (d - 1) by {
            apply(integer::le_transitive((truncating_quotient(n, d) * d), n, (bound * d) + (d - 1))) using { (truncating_quotient(n, d) * d) <= n; n <= (bound * d) + (d - 1); d != 0; };
        }
        have 0 < d by {
            have 0 + 1 <= d by {
                known();
            }
            apply(integer::step_le_lt(0, d)) using { 0 + 1 <= d; };
        }
        have (d - 1) < d by {
            known();
        }
        apply(integer::round_down_le(truncating_quotient(n, d), bound, d, (d - 1))) using { 0 < d; (d - 1) < d; (truncating_quotient(n, d) * d) <= (bound * d) + (d - 1); d != 0; };
    }
}

theorem positive_divisor_quotient_lower_rounded(n: Integer, d: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires n <= 0;
    requires (bound * d) - (d - 1) <= n;
    ensures bound <= truncating_quotient(n, d) by {
        have n == (truncating_quotient(n, d) * d) + truncating_remainder(n, d) by {
            apply(integer::truncation_identity(n, d)) using { d != 0; };
        }
        have n + -(truncating_remainder(n, d)) == (truncating_quotient(n, d) * d) by {
            apply(integer::sum_difference(n, (truncating_quotient(n, d) * d), truncating_remainder(n, d))) using { n == (truncating_quotient(n, d) * d) + truncating_remainder(n, d); d != 0; };
        }
        have -(truncating_quotient(n, d) * d) == -n + truncating_remainder(n, d) by {
            apply(integer::sum_difference(n, (truncating_quotient(n, d) * d), truncating_remainder(n, d))) using { n == (truncating_quotient(n, d) * d) + truncating_remainder(n, d); d != 0; };
        }
        have n == truncating_remainder(n, d) + (truncating_quotient(n, d) * d) by {
            apply(integer::sum_commute(n, (truncating_quotient(n, d) * d), truncating_remainder(n, d))) using { n == (truncating_quotient(n, d) * d) + truncating_remainder(n, d); d != 0; };
        }
        have truncating_remainder(n, d) <= 0 by {
            apply(integer::nonpositive_dividend_remainder(n, d)) using { d != 0; n <= 0; };
        }
        have truncating_remainder(n, d) + (truncating_quotient(n, d) * d) <= 0 + (truncating_quotient(n, d) * d) by {
            apply(integer::add_le(truncating_remainder(n, d), 0, (truncating_quotient(n, d) * d), (truncating_quotient(n, d) * d))) using { truncating_remainder(n, d) <= 0; (truncating_quotient(n, d) * d) <= (truncating_quotient(n, d) * d); d != 0; };
        }
        have n <= (truncating_quotient(n, d) * d) by {
            have n == truncating_remainder(n, d) + (truncating_quotient(n, d) * d) by {
                known();
            }
            have (truncating_quotient(n, d) * d) == 0 + (truncating_quotient(n, d) * d) by {
                known();
            }
            apply(integer::le_substitute(truncating_remainder(n, d) + (truncating_quotient(n, d) * d), 0 + (truncating_quotient(n, d) * d), n, (truncating_quotient(n, d) * d))) using { truncating_remainder(n, d) + (truncating_quotient(n, d) * d) <= 0 + (truncating_quotient(n, d) * d); n == truncating_remainder(n, d) + (truncating_quotient(n, d) * d); (truncating_quotient(n, d) * d) == 0 + (truncating_quotient(n, d) * d); d != 0; };
        }
        have (bound * d) - (d - 1) <= (truncating_quotient(n, d) * d) by {
            apply(integer::le_transitive((bound * d) - (d - 1), n, (truncating_quotient(n, d) * d))) using { (bound * d) - (d - 1) <= n; n <= (truncating_quotient(n, d) * d); d != 0; };
        }
        have -(truncating_quotient(n, d) * d) <= -((bound * d) - (d - 1)) by {
            apply(integer::negate_order((bound * d) - (d - 1), (truncating_quotient(n, d) * d))) using { (bound * d) - (d - 1) <= (truncating_quotient(n, d) * d); d != 0; };
        }
        have -(truncating_quotient(n, d)) * d == -(truncating_quotient(n, d) * d) by {
            apply(integer::negate_multiply(truncating_quotient(n, d), d)) using { d != 0; };
        }
        have -bound * d == -(bound * d) by {
            apply(integer::negate_multiply(bound, d));
        }
        have -(truncating_quotient(n, d)) * d <= -bound * d + (d - 1) by {
            have -(truncating_quotient(n, d)) * d == -(truncating_quotient(n, d) * d) by {
                rewrite(-(truncating_quotient(n, d)) * d, -(truncating_quotient(n, d) * d));
                known();
            }
            have -bound * d + (d - 1) == -((bound * d) - (d - 1)) by {
                rewrite(-bound * d, -(bound * d));
                known();
            }
            apply(integer::le_substitute(-(truncating_quotient(n, d) * d), -((bound * d) - (d - 1)), -(truncating_quotient(n, d)) * d, -bound * d + (d - 1))) using { -(truncating_quotient(n, d) * d) <= -((bound * d) - (d - 1)); -(truncating_quotient(n, d)) * d == -(truncating_quotient(n, d) * d); -bound * d + (d - 1) == -((bound * d) - (d - 1)); d != 0; };
        }
        have 0 < d by {
            have 0 + 1 <= d by {
                known();
            }
            apply(integer::step_le_lt(0, d)) using { 0 + 1 <= d; };
        }
        have (d - 1) < d by {
            known();
        }
        have -(truncating_quotient(n, d)) <= -bound by {
            apply(integer::round_down_le(-(truncating_quotient(n, d)), -bound, d, (d - 1))) using { 0 < d; (d - 1) < d; -(truncating_quotient(n, d)) * d <= -bound * d + (d - 1); d != 0; };
        }
        have -(-bound) <= -(-(truncating_quotient(n, d))) by {
            apply(integer::negate_order(-(truncating_quotient(n, d)), -bound)) using { -(truncating_quotient(n, d)) <= -bound; d != 0; };
        }
        have bound == -(-bound) by {
            known();
        }
        have truncating_quotient(n, d) == -(-(truncating_quotient(n, d))) by {
            known();
        }
        apply(integer::le_substitute(-(-bound), -(-(truncating_quotient(n, d))), bound, truncating_quotient(n, d))) using { -(-bound) <= -(-(truncating_quotient(n, d))); bound == -(-bound); truncating_quotient(n, d) == -(-(truncating_quotient(n, d))); d != 0; };
    }
}

theorem nonnegative_dividend_remainder_upper(n: Integer, d: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires 0 <= n;
    ensures truncating_remainder(n, d) <= n by {
        have 0 < d by {
            have 0 + 1 <= d by {
                known();
            }
            apply(integer::step_le_lt(0, d)) using { 0 + 1 <= d; };
        }
        have 0 <= d by {
            apply(integer::lt_le(0, d)) using { 0 < d; };
        }
        have n == (truncating_quotient(n, d) * d) + truncating_remainder(n, d) by {
            apply(integer::truncation_identity(n, d)) using { d != 0; };
        }
        have n + -(truncating_remainder(n, d)) == (truncating_quotient(n, d) * d) by {
            apply(integer::sum_difference(n, (truncating_quotient(n, d) * d), truncating_remainder(n, d))) using { n == (truncating_quotient(n, d) * d) + truncating_remainder(n, d); d != 0; };
        }
        have -(truncating_quotient(n, d) * d) == -n + truncating_remainder(n, d) by {
            apply(integer::sum_difference(n, (truncating_quotient(n, d) * d), truncating_remainder(n, d))) using { n == (truncating_quotient(n, d) * d) + truncating_remainder(n, d); d != 0; };
        }
        have n == truncating_remainder(n, d) + (truncating_quotient(n, d) * d) by {
            apply(integer::sum_commute(n, (truncating_quotient(n, d) * d), truncating_remainder(n, d))) using { n == (truncating_quotient(n, d) * d) + truncating_remainder(n, d); d != 0; };
        }
        have 0 * d == 0 by {
            known();
        }
        have 0 * d <= n by {
            rewrite(0 * d, 0);
            known();
        }
        have 0 <= truncating_quotient(n, d) by {
            apply(integer::positive_divisor_quotient_lower(n, d, 0)) using { d != 0; 1 <= d; 0 * d <= n; };
        }
        have 0 * d <= (truncating_quotient(n, d) * d) by {
            apply(integer::multiply_order_nonnegative(0, truncating_quotient(n, d), d)) using { 0 <= truncating_quotient(n, d); 0 <= d; d != 0; };
        }
        have 0 <= (truncating_quotient(n, d) * d) by {
            rewrite(0, 0 * d);
            known();
        }
        have 0 + truncating_remainder(n, d) <= (truncating_quotient(n, d) * d) + truncating_remainder(n, d) by {
            apply(integer::add_le(0, (truncating_quotient(n, d) * d), truncating_remainder(n, d), truncating_remainder(n, d))) using { 0 <= (truncating_quotient(n, d) * d); truncating_remainder(n, d) <= truncating_remainder(n, d); d != 0; };
        }
        have truncating_remainder(n, d) == 0 + truncating_remainder(n, d) by {
            known();
        }
        have n == (truncating_quotient(n, d) * d) + truncating_remainder(n, d) by {
            known();
        }
        apply(integer::le_substitute(0 + truncating_remainder(n, d), (truncating_quotient(n, d) * d) + truncating_remainder(n, d), truncating_remainder(n, d), n)) using { 0 + truncating_remainder(n, d) <= (truncating_quotient(n, d) * d) + truncating_remainder(n, d); truncating_remainder(n, d) == 0 + truncating_remainder(n, d); n == (truncating_quotient(n, d) * d) + truncating_remainder(n, d); d != 0; };
    }
}

theorem nonpositive_dividend_remainder_lower(n: Integer, d: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires n <= 0;
    ensures n <= truncating_remainder(n, d) by {
        have 0 < d by {
            have 0 + 1 <= d by {
                known();
            }
            apply(integer::step_le_lt(0, d)) using { 0 + 1 <= d; };
        }
        have 0 <= d by {
            apply(integer::lt_le(0, d)) using { 0 < d; };
        }
        have n == (truncating_quotient(n, d) * d) + truncating_remainder(n, d) by {
            apply(integer::truncation_identity(n, d)) using { d != 0; };
        }
        have n + -(truncating_remainder(n, d)) == (truncating_quotient(n, d) * d) by {
            apply(integer::sum_difference(n, (truncating_quotient(n, d) * d), truncating_remainder(n, d))) using { n == (truncating_quotient(n, d) * d) + truncating_remainder(n, d); d != 0; };
        }
        have -(truncating_quotient(n, d) * d) == -n + truncating_remainder(n, d) by {
            apply(integer::sum_difference(n, (truncating_quotient(n, d) * d), truncating_remainder(n, d))) using { n == (truncating_quotient(n, d) * d) + truncating_remainder(n, d); d != 0; };
        }
        have n == truncating_remainder(n, d) + (truncating_quotient(n, d) * d) by {
            apply(integer::sum_commute(n, (truncating_quotient(n, d) * d), truncating_remainder(n, d))) using { n == (truncating_quotient(n, d) * d) + truncating_remainder(n, d); d != 0; };
        }
        have 0 * d == 0 by {
            known();
        }
        have n <= 0 * d by {
            rewrite(0 * d, 0);
            known();
        }
        have truncating_quotient(n, d) <= 0 by {
            apply(integer::positive_divisor_quotient_upper(n, d, 0)) using { d != 0; 1 <= d; n <= 0 * d; };
        }
        have (truncating_quotient(n, d) * d) <= 0 * d by {
            apply(integer::multiply_order_nonnegative(truncating_quotient(n, d), 0, d)) using { truncating_quotient(n, d) <= 0; 0 <= d; d != 0; };
        }
        have (truncating_quotient(n, d) * d) <= 0 by {
            rewrite(0, 0 * d);
            known();
        }
        have (truncating_quotient(n, d) * d) + truncating_remainder(n, d) <= 0 + truncating_remainder(n, d) by {
            apply(integer::add_le((truncating_quotient(n, d) * d), 0, truncating_remainder(n, d), truncating_remainder(n, d))) using { (truncating_quotient(n, d) * d) <= 0; truncating_remainder(n, d) <= truncating_remainder(n, d); d != 0; };
        }
        have n == (truncating_quotient(n, d) * d) + truncating_remainder(n, d) by {
            known();
        }
        have truncating_remainder(n, d) == 0 + truncating_remainder(n, d) by {
            known();
        }
        apply(integer::le_substitute((truncating_quotient(n, d) * d) + truncating_remainder(n, d), 0 + truncating_remainder(n, d), n, truncating_remainder(n, d))) using { (truncating_quotient(n, d) * d) + truncating_remainder(n, d) <= 0 + truncating_remainder(n, d); n == (truncating_quotient(n, d) * d) + truncating_remainder(n, d); truncating_remainder(n, d) == 0 + truncating_remainder(n, d); d != 0; };
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
                apply(integer::multiply_order_nonnegative(endpoint, d, bound)) using { endpoint <= d; 0 <= bound; };
            }
            have bound * endpoint == endpoint * bound by {
                apply(integer::multiply_commutative(bound, endpoint));
            }
            have bound * d == d * bound by {
                apply(integer::multiply_commutative(bound, d));
            }
            have bound * endpoint == endpoint * bound by {
                rewrite(bound * endpoint, endpoint * bound);
                known();
            }
            have bound * d == d * bound by {
                rewrite(bound * d, d * bound);
                known();
            }
            apply(integer::le_substitute(endpoint * bound, d * bound, bound * endpoint, bound * d)) using { endpoint * bound <= d * bound; bound * endpoint == endpoint * bound; bound * d == d * bound; };
        }
        have endpoint - 1 <= d - 1 by {
            apply(integer::subtract_right_order(endpoint, d, 1)) using { endpoint <= d; };
        }
        have bound * endpoint + (endpoint - 1) <= bound * d + (d - 1) by {
            apply(integer::add_le(bound * endpoint, bound * d, endpoint - 1, d - 1)) using { bound * endpoint <= bound * d; endpoint - 1 <= d - 1; };
        }
        have numerator_bound <= bound * d + (d - 1) by {
            apply(integer::le_transitive(numerator_bound, bound * endpoint + (endpoint - 1), bound * d + (d - 1))) using { numerator_bound <= bound * endpoint + (endpoint - 1); bound * endpoint + (endpoint - 1) <= bound * d + (d - 1); };
        }
        have n <= bound * d + (d - 1) by {
            apply(integer::le_transitive(n, numerator_bound, bound * d + (d - 1))) using { n <= numerator_bound; numerator_bound <= bound * d + (d - 1); };
        }
        if n <= 0 {
            have 0 * d == 0 by {
                known();
            }
            have n <= 0 * d by {
                rewrite(0 * d, 0);
                known();
            }
            have truncating_quotient(n, d) <= 0 by {
                apply(integer::positive_divisor_quotient_upper(n, d, 0)) using { d != 0; 1 <= d; n <= 0 * d; };
            }
            apply(integer::le_transitive(truncating_quotient(n, d), 0, bound)) using { truncating_quotient(n, d) <= 0; 0 <= bound; d != 0; };
        } else {
            have 0 < n by {
                known();
            }
            have 0 <= n by {
                apply(integer::lt_le(0, n)) using { 0 < n; };
            }
            apply(integer::positive_divisor_quotient_upper_rounded(n, d, bound)) using { d != 0; 1 <= d; 0 <= n; n <= bound * d + (d - 1); };
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
                apply(integer::multiply_order_nonpositive(endpoint, d, bound)) using { endpoint <= d; bound <= 0; };
            }
            have bound * d == d * bound by {
                apply(integer::multiply_commutative(bound, d));
            }
            have bound * endpoint == endpoint * bound by {
                apply(integer::multiply_commutative(bound, endpoint));
            }
            have bound * d == d * bound by {
                rewrite(bound * d, d * bound);
                known();
            }
            have bound * endpoint == endpoint * bound by {
                rewrite(bound * endpoint, endpoint * bound);
                known();
            }
            apply(integer::le_substitute(d * bound, endpoint * bound, bound * d, bound * endpoint)) using { d * bound <= endpoint * bound; bound * d == d * bound; bound * endpoint == endpoint * bound; };
        }
        have endpoint - 1 <= d - 1 by {
            apply(integer::subtract_right_order(endpoint, d, 1)) using { endpoint <= d; };
        }
        have -(d - 1) <= -(endpoint - 1) by {
            apply(integer::negate_order(endpoint - 1, d - 1)) using { endpoint - 1 <= d - 1; };
        }
        have bound * d + -(d - 1) <= bound * endpoint + -(endpoint - 1) by {
            apply(integer::add_le(bound * d, bound * endpoint, -(d - 1), -(endpoint - 1))) using { bound * d <= bound * endpoint; -(d - 1) <= -(endpoint - 1); };
        }
        have bound * d - (d - 1) <= bound * endpoint - (endpoint - 1) by {
            have bound * d - (d - 1) == bound * d + -(d - 1) by {
                known();
            }
            have bound * endpoint - (endpoint - 1) == bound * endpoint + -(endpoint - 1) by {
                known();
            }
            apply(integer::le_substitute(bound * d + -(d - 1), bound * endpoint + -(endpoint - 1), bound * d - (d - 1), bound * endpoint - (endpoint - 1))) using { bound * d + -(d - 1) <= bound * endpoint + -(endpoint - 1); bound * d - (d - 1) == bound * d + -(d - 1); bound * endpoint - (endpoint - 1) == bound * endpoint + -(endpoint - 1); };
        }
        have bound * d - (d - 1) <= numerator_bound by {
            apply(integer::le_transitive(bound * d - (d - 1), bound * endpoint - (endpoint - 1), numerator_bound)) using { bound * d - (d - 1) <= bound * endpoint - (endpoint - 1); bound * endpoint - (endpoint - 1) <= numerator_bound; };
        }
        have bound * d - (d - 1) <= n by {
            apply(integer::le_transitive(bound * d - (d - 1), numerator_bound, n)) using { bound * d - (d - 1) <= numerator_bound; numerator_bound <= n; };
        }
        if 0 <= n {
            have 0 * d == 0 by {
                known();
            }
            have 0 * d <= n by {
                rewrite(0 * d, 0);
                known();
            }
            have 0 <= truncating_quotient(n, d) by {
                apply(integer::positive_divisor_quotient_lower(n, d, 0)) using { d != 0; 1 <= d; 0 * d <= n; };
            }
            apply(integer::le_transitive(bound, 0, truncating_quotient(n, d))) using { bound <= 0; 0 <= truncating_quotient(n, d); d != 0; };
        } else {
            have n < 0 by {
                known();
            }
            have n <= 0 by {
                apply(integer::lt_le(n, 0)) using { n < 0; };
            }
            apply(integer::positive_divisor_quotient_lower_rounded(n, d, bound)) using { d != 0; 1 <= d; n <= 0; bound * d - (d - 1) <= n; };
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
                apply(integer::multiply_order_nonpositive(d, endpoint, bound)) using { d <= endpoint; bound <= 0; };
            }
            have bound * endpoint == endpoint * bound by {
                apply(integer::multiply_commutative(bound, endpoint));
            }
            have bound * d == d * bound by {
                apply(integer::multiply_commutative(bound, d));
            }
            have bound * endpoint == endpoint * bound by {
                rewrite(bound * endpoint, endpoint * bound);
                known();
            }
            have bound * d == d * bound by {
                rewrite(bound * d, d * bound);
                known();
            }
            apply(integer::le_substitute(endpoint * bound, d * bound, bound * endpoint, bound * d)) using { endpoint * bound <= d * bound; bound * endpoint == endpoint * bound; bound * d == d * bound; };
        }
        have n <= bound * endpoint by {
            apply(integer::le_transitive(n, numerator_bound, bound * endpoint)) using { n <= numerator_bound; numerator_bound <= bound * endpoint; };
        }
        have n <= bound * d by {
            apply(integer::le_transitive(n, bound * endpoint, bound * d)) using { n <= bound * endpoint; bound * endpoint <= bound * d; };
        }
        apply(integer::positive_divisor_quotient_upper(n, d, bound)) using { d != 0; 1 <= d; n <= bound * d; };
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
                apply(integer::multiply_order_nonnegative(d, endpoint, bound)) using { d <= endpoint; 0 <= bound; };
            }
            have bound * d == d * bound by {
                apply(integer::multiply_commutative(bound, d));
            }
            have bound * endpoint == endpoint * bound by {
                apply(integer::multiply_commutative(bound, endpoint));
            }
            have bound * d == d * bound by {
                rewrite(bound * d, d * bound);
                known();
            }
            have bound * endpoint == endpoint * bound by {
                rewrite(bound * endpoint, endpoint * bound);
                known();
            }
            apply(integer::le_substitute(d * bound, endpoint * bound, bound * d, bound * endpoint)) using { d * bound <= endpoint * bound; bound * d == d * bound; bound * endpoint == endpoint * bound; };
        }
        have bound * d <= numerator_bound by {
            apply(integer::le_transitive(bound * d, bound * endpoint, numerator_bound)) using { bound * d <= bound * endpoint; bound * endpoint <= numerator_bound; };
        }
        have bound * d <= n by {
            apply(integer::le_transitive(bound * d, numerator_bound, n)) using { bound * d <= numerator_bound; numerator_bound <= n; };
        }
        apply(integer::positive_divisor_quotient_lower(n, d, bound)) using { d != 0; 1 <= d; bound * d <= n; };
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
                apply(integer::nonpositive_dividend_remainder_lower(n, d)) using { d != 0; 1 <= d; n <= 0; };
            }
            have bound <= n by {
                apply(integer::le_transitive(bound, numerator_bound, n)) using { bound <= numerator_bound; numerator_bound <= n; };
            }
            apply(integer::le_transitive(bound, n, truncating_remainder(n, d))) using { bound <= n; n <= truncating_remainder(n, d); d != 0; };
        } else {
            have 0 < n by {
                known();
            }
            have 0 <= n by {
                apply(integer::lt_le(0, n)) using { 0 < n; };
            }
            have 0 <= truncating_remainder(n, d) by {
                apply(integer::nonnegative_dividend_remainder(n, d)) using { d != 0; 0 <= n; };
            }
            apply(integer::le_transitive(bound, 0, truncating_remainder(n, d))) using { bound <= 0; 0 <= truncating_remainder(n, d); d != 0; };
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
                known();
            }
            apply(integer::step_le_lt(0, d)) using { 0 + 1 <= d; };
        }
        have 1 - d <= truncating_remainder(n, d) by {
            apply(integer::positive_divisor_remainder_lower(n, d)) using { d != 0; 0 < d; };
        }
        have 1 - endpoint <= 1 - d by {
            apply(integer::subtract_left_order(d, endpoint, 1)) using { d <= endpoint; };
        }
        have bound <= 1 - d by {
            apply(integer::le_transitive(bound, 1 - endpoint, 1 - d)) using { bound <= 1 - endpoint; 1 - endpoint <= 1 - d; };
        }
        apply(integer::le_transitive(bound, 1 - d, truncating_remainder(n, d))) using { bound <= 1 - d; 1 - d <= truncating_remainder(n, d); d != 0; };
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
                apply(integer::nonnegative_dividend_remainder_upper(n, d)) using { d != 0; 1 <= d; 0 <= n; };
            }
            have n <= bound by {
                apply(integer::le_transitive(n, numerator_bound, bound)) using { n <= numerator_bound; numerator_bound <= bound; };
            }
            apply(integer::le_transitive(truncating_remainder(n, d), n, bound)) using { truncating_remainder(n, d) <= n; n <= bound; d != 0; };
        } else {
            have n < 0 by {
                known();
            }
            have n <= 0 by {
                apply(integer::lt_le(n, 0)) using { n < 0; };
            }
            have truncating_remainder(n, d) <= 0 by {
                apply(integer::nonpositive_dividend_remainder(n, d)) using { d != 0; n <= 0; };
            }
            apply(integer::le_transitive(truncating_remainder(n, d), 0, bound)) using { truncating_remainder(n, d) <= 0; 0 <= bound; d != 0; };
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
                known();
            }
            apply(integer::step_le_lt(0, d)) using { 0 + 1 <= d; };
        }
        have truncating_remainder(n, d) <= d - 1 by {
            apply(integer::positive_divisor_remainder_upper(n, d)) using { d != 0; 0 < d; };
        }
        have d - 1 <= endpoint - 1 by {
            apply(integer::subtract_right_order(d, endpoint, 1)) using { d <= endpoint; };
        }
        have truncating_remainder(n, d) <= endpoint - 1 by {
            apply(integer::le_transitive(truncating_remainder(n, d), d - 1, endpoint - 1)) using { truncating_remainder(n, d) <= d - 1; d - 1 <= endpoint - 1; d != 0; };
        }
        apply(integer::le_transitive(truncating_remainder(n, d), endpoint - 1, bound)) using { truncating_remainder(n, d) <= endpoint - 1; endpoint - 1 <= bound; d != 0; };
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
                known();
            }
            rewrite(0 * endpoint - (endpoint - 1), 1 - endpoint);
            known();
        }
        have hi_n <= 0 * endpoint + (endpoint - 1) by {
            have 0 * endpoint + (endpoint - 1) == endpoint - 1 by {
                known();
            }
            rewrite(0 * endpoint + (endpoint - 1), endpoint - 1);
            known();
        }
        have 0 <= truncating_quotient(n, d) by {
            apply(integer::quotient_lower_interval_nonpositive(n, d, lo_n, endpoint, 0)) using { d != 0; 1 <= d; 0 <= 0; endpoint <= d; lo_n <= n; 0 * endpoint - (endpoint - 1) <= lo_n; };
        }
        have truncating_quotient(n, d) <= 0 by {
            apply(integer::quotient_upper_interval_nonnegative(n, d, hi_n, endpoint, 0)) using { d != 0; 1 <= d; 0 <= 0; endpoint <= d; n <= hi_n; hi_n <= 0 * endpoint + (endpoint - 1); };
        }
        have truncating_quotient(n, d) == 0 by {
            apply(integer::le_antisymmetric(truncating_quotient(n, d), 0)) using { truncating_quotient(n, d) <= 0; 0 <= truncating_quotient(n, d); d != 0; };
        }
        have n == (truncating_quotient(n, d) * d) + truncating_remainder(n, d) by {
            apply(integer::truncation_identity(n, d)) using { d != 0; };
        }
        have truncating_remainder(n, d) == (truncating_quotient(n, d) * d) + truncating_remainder(n, d) by {
            rewrite(truncating_quotient(n, d), 0);
            known();
        }
        have (truncating_quotient(n, d) * d) + truncating_remainder(n, d) == n by {
            known();
        }
        apply(integer::equal_substitute((truncating_quotient(n, d) * d) + truncating_remainder(n, d), n, truncating_remainder(n, d), n)) using { (truncating_quotient(n, d) * d) + truncating_remainder(n, d) == n; truncating_remainder(n, d) == (truncating_quotient(n, d) * d) + truncating_remainder(n, d); n == n; d != 0; };
    }
}

theorem nonzero_from_one(d: Integer) {
    requires 1 <= d;
    let one: Integer = 1;
    ensures d != 0 by {
        if d == 0 {
            have one <= 0 by {
                apply(integer::le_substitute(one, d, one, 0)) using { one <= d; one == one; 0 == d; };
            }
            contradiction(one <= 0);
        } else { known(); }
    }
}
theorem nonzero_from_negative_one(d: Integer) {
    requires d <= -1;
    let zero: Integer = 0;
    ensures d != 0 by {
        if d == 0 {
            have zero <= -1 by {
                apply(integer::le_substitute(d, -1, zero, -1)) using { d <= -1; zero == d; -1 == -1; };
            }
            contradiction(zero <= -1);
        } else { known(); }
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
            apply(integer::add_le(q * d, q * d, 0, r)) using { q * d <= q * d; 0 <= r; };
        }
        have q * d == q * d + 0 by known();
        have q * d <= n by {
            apply(integer::le_substitute(q * d + 0, q * d + r, q * d, n)) using {
                q * d + 0 <= q * d + r; q * d == q * d + 0; n == q * d + r;
            };
        }
        have q <= truncating_quotient(n, d) by {
            apply(integer::positive_divisor_quotient_lower(n, d, q)) using { d != 0; 1 <= d; q * d <= n; };
        }
        have q * d + r <= q * d + (d - 1) by {
            apply(integer::add_le(q * d, q * d, r, d - 1)) using { q * d <= q * d; r <= d - 1; };
        }
        have n <= q * d + (d - 1) by {
            apply(integer::le_substitute(q * d + r, q * d + (d - 1), n, q * d + (d - 1))) using {
                q * d + r <= q * d + (d - 1); n == q * d + r; q * d + (d - 1) == q * d + (d - 1);
            };
        }
        have truncating_quotient(n, d) <= q by {
            apply(integer::positive_divisor_quotient_upper_rounded(n, d, q)) using {
                d != 0; 1 <= d; 0 <= n; n <= q * d + (d - 1);
            };
        }
        apply(integer::le_antisymmetric(truncating_quotient(n, d), q)) using {
            truncating_quotient(n, d) <= q; q <= truncating_quotient(n, d); d != 0;
        };
    }
}

theorem nonnegative_quotient_shift(x: Integer, d: Integer, k: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires 0 <= x;
    requires 0 <= k;
    ensures truncating_quotient(x + d * k, d) == truncating_quotient(x, d) + k by {
        have 0 <= d by { apply(integer::le_transitive(0, 1, d)) using { 0 <= 1; 1 <= d; }; }
        have 0 * d <= k * d by {
            apply(integer::multiply_order_nonnegative(0, k, d)) using { 0 <= k; 0 <= d; };
        }
        have 0 * d == 0 by known();
        have d * k == k * d by { apply(integer::multiply_commutative(d, k)); }
        have 0 <= d * k by {
            apply(integer::le_substitute(0 * d, k * d, 0, d * k)) using { 0 * d <= k * d; 0 == 0 * d; d * k == k * d; };
        }
        have 0 + 0 <= x + d * k by {
            apply(integer::add_le(0, x, 0, d * k)) using { 0 <= x; 0 <= d * k; };
        }
        have 0 + 0 == 0 by known();
        have 0 <= x + d * k by known();
        have x == truncating_quotient(x, d) * d + truncating_remainder(x, d) by {
            apply(integer::truncation_identity(x, d)) using { d != 0; };
        }
        have 0 <= truncating_remainder(x, d) by {
            apply(integer::nonnegative_dividend_remainder(x, d)) using { d != 0; 0 <= x; };
        }
        have 0 < d by { apply(integer::step_le_lt(0, d)) using { 0 + 1 <= d; }; }
        have truncating_remainder(x, d) <= d - 1 by {
            apply(integer::positive_divisor_remainder_upper(x, d)) using { d != 0; 0 < d; };
        }
        have x + d * k == (truncating_quotient(x, d) * d + truncating_remainder(x, d)) + d * k by {
            apply(integer::equal_add(x, truncating_quotient(x, d) * d + truncating_remainder(x, d), d * k, d * k)) using {
                x == truncating_quotient(x, d) * d + truncating_remainder(x, d); d * k == d * k; d != 0;
            };
        }
        have (truncating_quotient(x, d) + k) * d == truncating_quotient(x, d) * d + k * d by {
            apply(integer::multiply_add(truncating_quotient(x, d), k, d)) using { d != 0; };
        }
        have (truncating_quotient(x, d) * d + truncating_remainder(x, d)) + d * k == (truncating_quotient(x, d) + k) * d + truncating_remainder(x, d) by {
            rewrite((truncating_quotient(x, d) + k) * d, truncating_quotient(x, d) * d + k * d);
            rewrite(d * k, k * d);
            known();
        }
        have x + d * k == (truncating_quotient(x, d) + k) * d + truncating_remainder(x, d) by known();
        apply(integer::nonnegative_quotient_from_remainder(x + d * k, d, truncating_quotient(x, d) + k, truncating_remainder(x, d))) using {
            d != 0; 1 <= d; 0 <= x + d * k;
            0 <= truncating_remainder(x, d); truncating_remainder(x, d) <= d - 1;
            x + d * k == (truncating_quotient(x, d) + k) * d + truncating_remainder(x, d);
        };
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
        apply(integer::nonnegative_quotient_from_remainder(n, d, q, r)) using {
            d != 0; 1 <= d; 0 <= n; 0 <= r; r <= d - 1; n == q * d + r;
        };
        apply(integer::truncation_identity(n, d)) using { d != 0; };
        have n == q * d + truncating_remainder(n, d) by known();
        have n == truncating_remainder(n, d) + q * d by {
            apply(integer::sum_commute(n, q * d, truncating_remainder(n, d))) using {
                n == q * d + truncating_remainder(n, d); d != 0;
            };
        }
        have n == r + q * d by {
            apply(integer::sum_commute(n, q * d, r)) using { n == q * d + r; };
        }
        apply(integer::sum_difference(n, truncating_remainder(n, d), q * d)) using {
            n == truncating_remainder(n, d) + q * d; d != 0;
        };
        apply(integer::sum_difference(n, r, q * d)) using { n == r + q * d; };
        known();
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
        apply(integer::int32_add_to_integer(i, j)) using { defined(i + j); };
        have (p + i) + 0 == p + i by known();
        have to_integer(j) - 0 == to_integer(i + j) - to_integer(i) by {
            rewrite(to_integer(i + j), to_integer(i) + to_integer(j));
            known();
        }
        apply(integer::uint8_pointer_translate_int32(p + i, p, 0, i, j, i + j)) using {
            (p + i) + 0 == p + i;
            to_integer(j) - 0 == to_integer(i + j) - to_integer(i);
            defined(i + j);
        };
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
        apply(integer::uint64_add_to_integer(i, j)) using { to_integer(i) + to_integer(j) <= 18446744073709551615; };
        have (p + i) + 0u64 == p + i by known();
        have to_integer(j) - 0 == to_integer(i + j) - to_integer(i) by {
            rewrite(to_integer(i + j), to_integer(i) + to_integer(j));
            known();
        }
        apply(integer::uint8_pointer_translate_uint64(p + i, p, 0u64, i, j, i + j)) using {
            (p + i) + 0u64 == p + i;
            to_integer(j) - 0 == to_integer(i + j) - to_integer(i);
            to_integer(i) + to_integer(j) <= 18446744073709551615;
        };
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
        apply(integer::int32_add_to_integer(i, j)) using { defined(i + j); };
        have (p + i) + 0 == p + i by known();
        have to_integer(j) - 0 == to_integer(i + j) - to_integer(i) by {
            rewrite(to_integer(i + j), to_integer(i) + to_integer(j));
            known();
        }
        apply(integer::int8_pointer_translate_int32(p + i, p, 0, i, j, i + j)) using {
            (p + i) + 0 == p + i;
            to_integer(j) - 0 == to_integer(i + j) - to_integer(i);
            defined(i + j);
        };
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
        apply(integer::uint64_add_to_integer(i, j)) using { to_integer(i) + to_integer(j) <= 18446744073709551615; };
        have (p + i) + 0u64 == p + i by known();
        have to_integer(j) - 0 == to_integer(i + j) - to_integer(i) by {
            rewrite(to_integer(i + j), to_integer(i) + to_integer(j));
            known();
        }
        apply(integer::int8_pointer_translate_uint64(p + i, p, 0u64, i, j, i + j)) using {
            (p + i) + 0u64 == p + i;
            to_integer(j) - 0 == to_integer(i + j) - to_integer(i);
            to_integer(i) + to_integer(j) <= 18446744073709551615;
        };
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
        apply(integer::int32_add_to_integer(i, j)) using { defined(i + j); };
        have (p + i) + 0 == p + i by known();
        have to_integer(j) - 0 == to_integer(i + j) - to_integer(i) by {
            rewrite(to_integer(i + j), to_integer(i) + to_integer(j));
            known();
        }
        apply(integer::uint16_pointer_translate_int32(p + i, p, 0, i, j, i + j)) using {
            (p + i) + 0 == p + i;
            to_integer(j) - 0 == to_integer(i + j) - to_integer(i);
            defined(i + j);
        };
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
        apply(integer::uint64_add_to_integer(i, j)) using { to_integer(i) + to_integer(j) <= 18446744073709551615; };
        have (p + i) + 0u64 == p + i by known();
        have to_integer(j) - 0 == to_integer(i + j) - to_integer(i) by {
            rewrite(to_integer(i + j), to_integer(i) + to_integer(j));
            known();
        }
        apply(integer::uint16_pointer_translate_uint64(p + i, p, 0u64, i, j, i + j)) using {
            (p + i) + 0u64 == p + i;
            to_integer(j) - 0 == to_integer(i + j) - to_integer(i);
            to_integer(i) + to_integer(j) <= 18446744073709551615;
        };
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
        apply(integer::int32_add_to_integer(i, j)) using { defined(i + j); };
        have (p + i) + 0 == p + i by known();
        have to_integer(j) - 0 == to_integer(i + j) - to_integer(i) by {
            rewrite(to_integer(i + j), to_integer(i) + to_integer(j));
            known();
        }
        apply(integer::int16_pointer_translate_int32(p + i, p, 0, i, j, i + j)) using {
            (p + i) + 0 == p + i;
            to_integer(j) - 0 == to_integer(i + j) - to_integer(i);
            defined(i + j);
        };
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
        apply(integer::uint64_add_to_integer(i, j)) using { to_integer(i) + to_integer(j) <= 18446744073709551615; };
        have (p + i) + 0u64 == p + i by known();
        have to_integer(j) - 0 == to_integer(i + j) - to_integer(i) by {
            rewrite(to_integer(i + j), to_integer(i) + to_integer(j));
            known();
        }
        apply(integer::int16_pointer_translate_uint64(p + i, p, 0u64, i, j, i + j)) using {
            (p + i) + 0u64 == p + i;
            to_integer(j) - 0 == to_integer(i + j) - to_integer(i);
            to_integer(i) + to_integer(j) <= 18446744073709551615;
        };
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
        apply(integer::int32_add_to_integer(i, j)) using { defined(i + j); };
        have (p + i) + 0 == p + i by known();
        have to_integer(j) - 0 == to_integer(i + j) - to_integer(i) by {
            rewrite(to_integer(i + j), to_integer(i) + to_integer(j));
            known();
        }
        apply(integer::uint32_pointer_translate_int32(p + i, p, 0, i, j, i + j)) using {
            (p + i) + 0 == p + i;
            to_integer(j) - 0 == to_integer(i + j) - to_integer(i);
            defined(i + j);
        };
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
        apply(integer::uint64_add_to_integer(i, j)) using { to_integer(i) + to_integer(j) <= 18446744073709551615; };
        have (p + i) + 0u64 == p + i by known();
        have to_integer(j) - 0 == to_integer(i + j) - to_integer(i) by {
            rewrite(to_integer(i + j), to_integer(i) + to_integer(j));
            known();
        }
        apply(integer::uint32_pointer_translate_uint64(p + i, p, 0u64, i, j, i + j)) using {
            (p + i) + 0u64 == p + i;
            to_integer(j) - 0 == to_integer(i + j) - to_integer(i);
            to_integer(i) + to_integer(j) <= 18446744073709551615;
        };
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
        apply(integer::int32_add_to_integer(i, j)) using { defined(i + j); };
        have (p + i) + 0 == p + i by known();
        have to_integer(j) - 0 == to_integer(i + j) - to_integer(i) by {
            rewrite(to_integer(i + j), to_integer(i) + to_integer(j));
            known();
        }
        apply(integer::int32_pointer_translate_int32(p + i, p, 0, i, j, i + j)) using {
            (p + i) + 0 == p + i;
            to_integer(j) - 0 == to_integer(i + j) - to_integer(i);
            defined(i + j);
        };
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
        apply(integer::uint64_add_to_integer(i, j)) using { to_integer(i) + to_integer(j) <= 18446744073709551615; };
        have (p + i) + 0u64 == p + i by known();
        have to_integer(j) - 0 == to_integer(i + j) - to_integer(i) by {
            rewrite(to_integer(i + j), to_integer(i) + to_integer(j));
            known();
        }
        apply(integer::int32_pointer_translate_uint64(p + i, p, 0u64, i, j, i + j)) using {
            (p + i) + 0u64 == p + i;
            to_integer(j) - 0 == to_integer(i + j) - to_integer(i);
            to_integer(i) + to_integer(j) <= 18446744073709551615;
        };
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
        apply(integer::int32_add_to_integer(i, j)) using { defined(i + j); };
        have (p + i) + 0 == p + i by known();
        have to_integer(j) - 0 == to_integer(i + j) - to_integer(i) by {
            rewrite(to_integer(i + j), to_integer(i) + to_integer(j));
            known();
        }
        apply(integer::uint64_pointer_translate_int32(p + i, p, 0, i, j, i + j)) using {
            (p + i) + 0 == p + i;
            to_integer(j) - 0 == to_integer(i + j) - to_integer(i);
            defined(i + j);
        };
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
        apply(integer::uint64_add_to_integer(i, j)) using { to_integer(i) + to_integer(j) <= 18446744073709551615; };
        have (p + i) + 0u64 == p + i by known();
        have to_integer(j) - 0 == to_integer(i + j) - to_integer(i) by {
            rewrite(to_integer(i + j), to_integer(i) + to_integer(j));
            known();
        }
        apply(integer::uint64_pointer_translate_uint64(p + i, p, 0u64, i, j, i + j)) using {
            (p + i) + 0u64 == p + i;
            to_integer(j) - 0 == to_integer(i + j) - to_integer(i);
            to_integer(i) + to_integer(j) <= 18446744073709551615;
        };
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
        apply(integer::int32_add_to_integer(i, j)) using { defined(i + j); };
        have (p + i) + 0 == p + i by known();
        have to_integer(j) - 0 == to_integer(i + j) - to_integer(i) by {
            rewrite(to_integer(i + j), to_integer(i) + to_integer(j));
            known();
        }
        apply(integer::int64_pointer_translate_int32(p + i, p, 0, i, j, i + j)) using {
            (p + i) + 0 == p + i;
            to_integer(j) - 0 == to_integer(i + j) - to_integer(i);
            defined(i + j);
        };
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
        apply(integer::uint64_add_to_integer(i, j)) using { to_integer(i) + to_integer(j) <= 18446744073709551615; };
        have (p + i) + 0u64 == p + i by known();
        have to_integer(j) - 0 == to_integer(i + j) - to_integer(i) by {
            rewrite(to_integer(i + j), to_integer(i) + to_integer(j));
            known();
        }
        apply(integer::int64_pointer_translate_uint64(p + i, p, 0u64, i, j, i + j)) using {
            (p + i) + 0u64 == p + i;
            to_integer(j) - 0 == to_integer(i + j) - to_integer(i);
            to_integer(i) + to_integer(j) <= 18446744073709551615;
        };
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
        apply(integer::int32_add_to_integer(i, j)) using { defined(i + j); };
        have (p + i) + 0 == p + i by known();
        have to_integer(j) - 0 == to_integer(i + j) - to_integer(i) by {
            rewrite(to_integer(i + j), to_integer(i) + to_integer(j));
            known();
        }
        apply(integer::float32_pointer_translate_int32(p + i, p, 0, i, j, i + j)) using {
            (p + i) + 0 == p + i;
            to_integer(j) - 0 == to_integer(i + j) - to_integer(i);
            defined(i + j);
        };
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
        apply(integer::uint64_add_to_integer(i, j)) using { to_integer(i) + to_integer(j) <= 18446744073709551615; };
        have (p + i) + 0u64 == p + i by known();
        have to_integer(j) - 0 == to_integer(i + j) - to_integer(i) by {
            rewrite(to_integer(i + j), to_integer(i) + to_integer(j));
            known();
        }
        apply(integer::float32_pointer_translate_uint64(p + i, p, 0u64, i, j, i + j)) using {
            (p + i) + 0u64 == p + i;
            to_integer(j) - 0 == to_integer(i + j) - to_integer(i);
            to_integer(i) + to_integer(j) <= 18446744073709551615;
        };
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
        apply(integer::int32_add_to_integer(i, j)) using { defined(i + j); };
        have (p + i) + 0 == p + i by known();
        have to_integer(j) - 0 == to_integer(i + j) - to_integer(i) by {
            rewrite(to_integer(i + j), to_integer(i) + to_integer(j));
            known();
        }
        apply(integer::float64_pointer_translate_int32(p + i, p, 0, i, j, i + j)) using {
            (p + i) + 0 == p + i;
            to_integer(j) - 0 == to_integer(i + j) - to_integer(i);
            defined(i + j);
        };
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
        apply(integer::uint64_add_to_integer(i, j)) using { to_integer(i) + to_integer(j) <= 18446744073709551615; };
        have (p + i) + 0u64 == p + i by known();
        have to_integer(j) - 0 == to_integer(i + j) - to_integer(i) by {
            rewrite(to_integer(i + j), to_integer(i) + to_integer(j));
            known();
        }
        apply(integer::float64_pointer_translate_uint64(p + i, p, 0u64, i, j, i + j)) using {
            (p + i) + 0u64 == p + i;
            to_integer(j) - 0 == to_integer(i + j) - to_integer(i);
            to_integer(i) + to_integer(j) <= 18446744073709551615;
        };
    }
}
