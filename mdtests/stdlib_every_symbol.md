# Every standard-library symbol

This fixture and the companion regressions named below give every public
declaration in the `library/` modules a checked use. The documentation
inventory separately checks that the source registry and library reference
remain complete.

The `authority` resource's restricted empty-population source use is verified
by `authority_establishes_and_retires_empty_stack_population` in
`src/surface/tests/execution_tests.rs`.

The representation law `integer::uint32_from_le_bytes` is exercised in
[`integer_uint32_from_le_bytes_initialization.md`](integer_uint32_from_le_bytes_initialization.md).

The separation axiom `separation::restrict` is verified in
[`resource_theorem_parameters.md`](resource_theorem_parameters.md), including
forwarding through a user theorem and application to C struct fields.
The element law `separation::elements` is verified in
[`separation_elements.md`](separation_elements.md) and
[`separation_elements_types.md`](separation_elements_types.md).
The generic range law `separation::subrange` is verified in
[`generic_pointer_theorem_parameters.md`](generic_pointer_theorem_parameters.md),
including nested generic applications and several element widths.

The external catalog symbols `memcmp` and `strlen` are verified in
[`strlen_of_an_empty_string_and_memcmp_use_the_catalog_contracts.md`](strlen_of_an_empty_string_and_memcmp_use_the_catalog_contracts.md),
`memcpy` in
[`byte_representation_scalar_copy.md`](byte_representation_scalar_copy.md),
and `memset`'s precondition is checked at a call in
[`c_builtin_memset_header_checks_its_contract.md`](c_builtin_memset_header_checks_its_contract.md).

The external catalog symbol `__click_constant_p_unknown`, the value of the C
builtin `__builtin_constant_p`, is verified in
[`c_builtin_constant_p.md`](c_builtin_constant_p.md).

The borrowed C-string resource `cstr_at` is verified in
[`cstr_at_view_passes_through_a_call.md`](cstr_at_view_passes_through_a_call.md),
[`cstr_at_opens_and_lends_a_prefix_to_a_copy.md`](cstr_at_opens_and_lends_a_prefix_to_a_copy.md),
and [`cstr_at_fold_refuses_a_wrong_length.md`](cstr_at_fold_refuses_a_wrong_length.md).

The modeled-runtime resource `mutex_guard` is verified in
[`mutex_guard_resource_body.md`](mutex_guard_resource_body.md) and
[`mutex_guard_conditional_body.md`](mutex_guard_conditional_body.md).

The modeled-runtime resource `mutex_live` is verified in
[`mutex_live_wrapper.md`](mutex_live_wrapper.md) and
[`mutex_live_contract.md`](mutex_live_contract.md).

The modeled-runtime resource `mutex_use` is verified in
[`mutex_use_contract.md`](mutex_use_contract.md) and
[`mutex_use_mixed.md`](mutex_use_mixed.md).

The modeled-runtime resources `publisher` and `subscriber` are verified in
[`publication_one_shot_handoff.md`](publication_one_shot_handoff.md).

```c filename=stdlib_every_symbol.c
int32 docs_identity(int32 value) {
    return value;
}
```

```click
import click::integer;
import click::permutation;
import click::cstr;
import click::bytes;
import click::format;
import click::rust::i8;
import click::rust::i16;
import click::rust::i32;
import click::rust::i64;
import click::rust::isize;
import click::rust::u8;
import click::rust::u16;
import click::rust::u32;
import click::rust::u64;
import click::rust::usize;

theorem use_uint32_less_equal_to_integer(left: uint32, right: uint32) {
    requires left <= right;
    ensures to_integer(left) <= to_integer(right) by {
        apply(integer::uint32_less_equal_to_integer(left, right));
    }
}
theorem use_uint32_less_equal_of_to_integer(left: uint32, right: uint32) {
    requires to_integer(left) <= to_integer(right);
    ensures left <= right by {
        apply(integer::uint32_to_integer_less_equal_implies_less_equal(left, right));
    }
}
theorem use_uint32_equal_of_to_integer(left: uint32, right: uint32) {
    requires to_integer(left) == to_integer(right);
    ensures left == right by {
        apply(integer::uint32_to_integer_equal_implies_equal(left, right));
    }
}
theorem use_uint32_to_integer_bounds(value: uint32) {
    ensures 0 <= to_integer(value) by apply(integer::uint32_to_integer_bounds(value));
    ensures to_integer(value) <= 4294967295 by apply(integer::uint32_to_integer_bounds(value));
}
theorem use_uint64_to_integer_bounds(value: uint64) {
    ensures 0 <= to_integer(value) by apply(integer::uint64_to_integer_bounds(value));
    ensures to_integer(value) <= 18446744073709551615 by apply(integer::uint64_to_integer_bounds(value));
}
theorem use_unsigned_reduction(value: uint32, divisor: uint32) {
    requires divisor != 0u32;
    ensures value % divisor < divisor by apply(integer::uint32_remainder_less_than_divisor(value, divisor));
    ensures 0 <= to_integer(value % divisor) by apply(integer::uint32_to_integer_bounds(value % divisor));
    ensures to_integer(value % divisor) < to_integer(divisor) by {
        apply(integer::uint32_remainder_less_than_divisor(value, divisor));
    }
}
theorem use_uint32_remainder_of_lt(value: uint32, divisor: uint32) {
    requires value < divisor;
    ensures value % divisor == value by apply(integer::uint32_less_than_divisor_implies_remainder_is_value(value, divisor));
}
theorem use_uint32_add_to_integer(left: uint32, right: uint32) {
    requires to_integer(left) + to_integer(right) <= 4294967295;
    ensures to_integer(left + right) == to_integer(left) + to_integer(right) by apply(integer::uint32_add_to_integer(left, right));
}

theorem use_uint32_subtract_to_integer(left: uint32, right: uint32) {
    requires right <= left;
    ensures to_integer(left - right) == to_integer(left) - to_integer(right) by {
        apply(integer::uint32_subtract_to_integer(left, right));
    }
}

theorem use_uint32_divide_to_integer(left: uint32, right: uint32) {
    requires right != 0u32;
    requires to_integer(right) != 0;
    ensures to_integer(left / right) == truncating_quotient(to_integer(left), to_integer(right)) by apply(integer::uint32_divide_to_integer(left, right));
}
theorem use_uint32_remainder_to_integer(left: uint32, right: uint32) {
    requires right != 0u32;
    requires to_integer(right) != 0;
    ensures to_integer(left % right) == truncating_remainder(to_integer(left), to_integer(right)) by apply(integer::uint32_remainder_to_integer(left, right));
}

theorem use_uint32_mul_to_integer(left: uint32, right: uint32) {
    requires right == 0u32 or left <= 4294967295u32 / right;
    ensures to_integer(left * right) == to_integer(left) * to_integer(right) by {
        apply(integer::uint32_multiply_to_integer(left, right));
    }
}

theorem use_uint32_mul_guard_by_integer_bound(left: uint32, right: uint32) {
    requires to_integer(left) * to_integer(right) <= 4294967295;
    ensures right == 0u32 or left <= 4294967295u32 / right by {
        apply(integer::uint32_multiply_guard_by_integer_bound(left, right)) using {
            to_integer(left) * to_integer(right) <= 4294967295;
        };
    }
}

theorem use_uint64_add_to_integer(left: uint64, right: uint64) {
    requires to_integer(left) + to_integer(right) <= 18446744073709551615;
    ensures to_integer(left + right) == to_integer(left) + to_integer(right) by apply(integer::uint64_add_to_integer(left, right));
}

theorem use_uint64_multiply_to_integer(left: uint64, right: uint64) {
    requires to_integer(left) * to_integer(right) <= 18446744073709551615;
    ensures to_integer(left * right) == to_integer(left) * to_integer(right) by apply(integer::uint64_multiply_to_integer(left, right));
}

theorem use_uint64_product_bound_from_division(x: uint64, y: uint64) {
    requires y != 0u64;
    requires x <= 18446744073709551615u64 / y;
    ensures to_integer(x) * to_integer(y) <= to_integer(18446744073709551615u64) by apply(integer::uint64_product_bound_from_division(x, y));
}

theorem use_uint64_subtract_to_integer(left: uint64, right: uint64) {
    requires to_integer(right) <= to_integer(left);
    ensures to_integer(left - right) == to_integer(left) - to_integer(right) by apply(integer::uint64_subtract_to_integer(left, right));
}

theorem use_uint64_divide_to_integer(left: uint64, right: uint64) {
    requires right != 0u64;
    requires to_integer(right) != 0;
    ensures to_integer(left / right) == truncating_quotient(to_integer(left), to_integer(right)) by apply(integer::uint64_divide_to_integer(left, right));
}

theorem use_uint64_remainder_to_integer(left: uint64, right: uint64) {
    requires right != 0u64;
    requires to_integer(right) != 0;
    ensures to_integer(left % right) == truncating_remainder(to_integer(left), to_integer(right)) by apply(integer::uint64_remainder_to_integer(left, right));
}

theorem use_uint64_less_equal_to_integer(left: uint64, right: uint64) {
    requires left <= right;
    ensures to_integer(left) <= to_integer(right) by apply(integer::uint64_less_equal_to_integer(left, right));
}

theorem use_uint64_less_equal_of_to_integer(left: uint64, right: uint64) {
    requires to_integer(left) <= to_integer(right);
    ensures left <= right by apply(integer::uint64_to_integer_less_equal_implies_less_equal(left, right));
}

theorem use_uint64_less_than_to_integer(left: uint64, right: uint64) {
    requires left < right;
    ensures to_integer(left) < to_integer(right) by apply(integer::uint64_less_than_to_integer(left, right));
}

theorem use_uint64_less_than_of_to_integer(left: uint64, right: uint64) {
    requires to_integer(left) < to_integer(right);
    ensures left < right by apply(integer::uint64_to_integer_less_than_implies_less_than(left, right));
}

theorem use_uint32_pack_u16_to_integer(low: uint32, high: uint32) {
    requires low <= 65535u32;
    requires high <= 65535u32;
    ensures to_integer(low | (high << 16)) == to_integer(low) + 65536 * to_integer(high) by apply(integer::uint32_pack_uint16_to_integer(low, high));
}

theorem use_uint32_pack_u16_high_first_to_integer(low: uint32, high: uint32) {
    requires low <= 65535u32;
    requires high <= 65535u32;
    ensures to_integer((high << 16) | low) == to_integer(low) + 65536 * to_integer(high) by apply(integer::uint32_pack_uint16_high_first_to_integer(low, high));
}

theorem use_uint32_unpack_u16_low(low: uint32, high: uint32) {
    requires low <= 65535u32;
    requires high <= 65535u32;
    ensures (((high << 16) | low) & 65535u32) == low by apply(integer::uint32_unpack_uint16_low(low, high));
}

theorem use_uint32_unpack_u16_high(low: uint32, high: uint32) {
    requires low <= 65535u32;
    requires high <= 65535u32;
    ensures ((((high << 16) | low) >> 16) & 65535u32) == high by apply(integer::uint32_unpack_uint16_high(low, high));
}

theorem use_uint64_pack_u16_to_integer(low: uint64, high: uint64) {
    requires low <= 65535u64;
    requires high <= 65535u64;
    ensures to_integer(low | (high << 16)) == to_integer(low) + 65536 * to_integer(high) by apply(integer::uint64_pack_uint16_to_integer(low, high));
}

theorem use_uint64_unpack_u16_low(low: uint64, high: uint64) {
    requires low <= 65535u64;
    requires high <= 65535u64;
    ensures ((low | (high << 16)) & 65535u64) == low by apply(integer::uint64_unpack_uint16_low(low, high));
}

theorem use_uint64_unpack_u16_high(low: uint64, high: uint64) {
    requires low <= 65535u64;
    requires high <= 65535u64;
    ensures (((low | (high << 16)) >> 16) & 65535u64) == high by apply(integer::uint64_unpack_uint16_high(low, high));
}

theorem use_uint64_not_greater_equal_of_less_than(left: uint64, right: uint64) {
    requires left < right;
    ensures not (left >= right) by apply(integer::uint64_less_than_implies_not_greater_equal(left, right));
}

theorem use_uint64_equal_of_to_integer(left: uint64, right: uint64) {
    requires to_integer(left) == to_integer(right);
    ensures left == right by apply(integer::uint64_to_integer_equal_implies_equal(left, right));
}

theorem use_int64_add_defined_by_integer_bounds(left: int64, right: int64) {
    requires to_integer(left) + to_integer(right) >= -9223372036854775808;
    requires to_integer(left) + to_integer(right) <= 9223372036854775807;
    ensures defined(left + right) by apply(integer::int64_add_defined_by_integer_bounds(left, right));
}

theorem use_int64_less_than_to_integer(left: int64, right: int64) {
    requires left < right;
    ensures to_integer(left) < to_integer(right) by apply(integer::int64_less_than_to_integer(left, right));
}

theorem use_int64_greater_equal_to_integer(left: int64, right: int64) {
    requires left >= right;
    ensures to_integer(left) >= to_integer(right) by apply(integer::int64_greater_equal_to_integer(left, right));
}

theorem use_floor_from_remainder(n: Integer, d: Integer, q: Integer, r: Integer, value: Integer) {
    requires 0 < d;
    requires n == q * d + r;
    requires 1 - d <= r;
    requires r <= d - 1;
    requires r < 0 implies value == q + -1;
    requires 0 <= r implies value == q;
    ensures value * d <= n by apply(integer::floor_from_remainder(n, d, q, r, value));
    ensures n < (value + 1) * d by apply(integer::floor_from_remainder(n, d, q, r, value));
}
theorem use_ceiling_from_remainder(n: Integer, d: Integer, q: Integer, r: Integer, value: Integer) {
    requires 0 < d;
    requires n == q * d + r;
    requires 1 - d <= r;
    requires r <= d - 1;
    requires 0 < r implies value == q + 1;
    requires r <= 0 implies value == q;
    ensures n <= value * d by apply(integer::ceiling_from_remainder(n, d, q, r, value));
    ensures (value + -1) * d < n by apply(integer::ceiling_from_remainder(n, d, q, r, value));
}
theorem use_multiply_add(a: Integer, b: Integer, c: Integer) {
    ensures (a + b) * c == a * c + b * c by apply(integer::multiply_add(a, b, c));
}
theorem check_truncation_identity(n: Integer, d: Integer) {
    requires d != 0;
    ensures n == truncating_quotient(n, d) * d + truncating_remainder(n, d) by {
        apply(integer::truncation_identity(n, d));
    }
}

theorem check_positive_divisor_remainder_lower(n: Integer, d: Integer) {
    requires d != 0;
    requires 0 < d;
    ensures 1 - d <= truncating_remainder(n, d) by {
        apply(integer::positive_divisor_remainder_lower(n, d));
    }
}

theorem check_positive_divisor_remainder_upper(n: Integer, d: Integer) {
    requires d != 0;
    requires 0 < d;
    ensures truncating_remainder(n, d) <= d - 1 by {
        apply(integer::positive_divisor_remainder_upper(n, d));
    }
}

theorem check_nonnegative_dividend_remainder(n: Integer, d: Integer) {
    requires d != 0;
    requires 0 <= n;
    ensures 0 <= truncating_remainder(n, d) by {
        apply(integer::nonnegative_dividend_remainder(n, d));
    }
}

theorem check_nonpositive_dividend_remainder(n: Integer, d: Integer) {
    requires d != 0;
    requires n <= 0;
    ensures truncating_remainder(n, d) <= 0 by {
        apply(integer::nonpositive_dividend_remainder(n, d));
    }
}
theorem exact64_difference(left: int64, right: int64) {
    requires defined(left - right);
    ensures to_integer(left - right) == to_integer(left) - to_integer(right) by {
        apply(integer::int64_subtract_to_integer(left, right));
    }
}

theorem integer_bounds_establish_c_add_safety(left: int32, right: int32) {
    requires to_integer(left) + to_integer(right) >= -2147483648;
    requires to_integer(left) + to_integer(right) <= 2147483647;
    ensures defined(left + right) by {
        apply(integer::int32_add_defined_by_integer_bounds(left, right));
    }
}

theorem integer_add_bridge(left: int32, right: int32) {
    requires defined(left + right);
    ensures to_integer(left + right) == to_integer(left) + to_integer(right) by {
        apply(integer::int32_add_to_integer(left, right));
    }
}

theorem reflect32(left: int32, right: int32) {
    requires to_integer(left) <= to_integer(right);
    ensures left <= right by apply(integer::int32_to_integer_less_equal_implies_less_equal(left, right));
}
theorem preserve64(left: int64, right: int64) {
    requires left <= right;
    ensures to_integer(left) <= to_integer(right) by apply(integer::int64_less_equal_to_integer(left, right));
}
theorem reflect64(left: int64, right: int64) {
    requires to_integer(left) <= to_integer(right);
    ensures left <= right by apply(integer::int64_to_integer_less_equal_implies_less_equal(left, right));
}
theorem equal64(left: int64, right: int64) {
    requires to_integer(left) == to_integer(right);
    ensures left == right by apply(integer::int64_to_integer_equal_implies_equal(left, right));
}

theorem integer_order_bridge(left: int32, right: int32) {
    requires left <= right;
    ensures to_integer(left) <= to_integer(right) by {
        apply(integer::int32_less_equal_to_integer(left, right));
    }
}

theorem integer_subtract_bridge(left: int32, right: int32) {
    requires defined(left - right);
    ensures to_integer(left - right) == to_integer(left) - to_integer(right) by {
        apply(integer::int32_subtract_to_integer(left, right));
    }
}

theorem builtin_nat_integer_laws(n: Nat) {
    ensures to_integer(Nat::Zero) == 0 by apply(nat::to_integer_zero());
    ensures to_integer(Nat::Succ(n)) == to_integer(n) + 1 by apply(nat::to_integer_succ(n));
    ensures to_integer(n) >= 0 by apply(nat::to_integer_nonnegative(n));
    ensures to_nat(to_integer(n)) == n by apply(nat::to_nat_to_integer(n));
    ensures to_nat(0) == Nat::Zero by apply(nat::to_nat_zero());
}

theorem builtin_integer_nat_laws(z: Integer) {
    requires z >= 0;
    ensures to_integer(to_nat(z)) == z by apply(nat::to_integer_to_nat(z));
}

theorem nat_laws(a: Nat, b: Nat, c: Nat) {
    ensures to_integer(nat::add(a, b)) == to_integer(a) + to_integer(b) by apply(nat::to_integer_add(a, b));
    ensures nat::add(Nat::Zero, a) == a by apply(nat::add_left_identity(a));
    ensures nat::add(a, Nat::Zero) == a by apply(nat::add_right_identity(a));
    ensures nat::add(Nat::Succ(a), b) == Nat::Succ(nat::add(a, b)) by apply(nat::add_succ_left(a, b));
    ensures nat::add(a, Nat::Succ(b)) == Nat::Succ(nat::add(a, b)) by apply(nat::add_succ_right(a, b));
    ensures nat::add(nat::add(a, b), c) == nat::add(a, nat::add(b, c)) by apply(nat::add_associative(a, b, c));
    ensures nat::add(a, b) == nat::add(b, a) by apply(nat::add_commutative(a, b));
}

theorem one_plus_one() {
    ensures nat::add(Nat::Succ(Nat::Zero), Nat::Succ(Nat::Zero))
        == Nat::Succ(Nat::Succ(Nat::Zero)) by {
        unfold(nat::add(Nat::Succ(Nat::Zero), Nat::Succ(Nat::Zero)));
        unfold(nat::add(Nat::Zero, Nat::Succ(Nat::Zero)));
        solve();
    }
}

theorem length_laws<T>(head: T, xs: List<T>, ys: List<T>) {
    ensures list::length(List<T>::Nil) == Nat::Zero by {
        apply(list::length_nil(List<T>::Nil));
    }
    ensures list::length(List<T>::Cons(head, xs)) == Nat::Succ(list::length(xs)) by {
        apply(list::length_cons(head, xs));
    }
    ensures list::length(list::append(xs, ys)) == nat::add(list::length(xs), list::length(ys)) by {
        apply(list::length_append(xs, ys));
    }
}

theorem nested_length(xs: List<List<int32>>, ys: List<List<int32>>) {
    ensures list::length(list::append(xs, ys)) == nat::add(list::length(xs), list::length(ys)) by {
        apply(list::length_append(xs, ys));
    }
}

theorem option_constructors(value: int32) {
    ensures Option<int32>::Some(value) != Option<int32>::None by {
        solve();
    }
}

theorem singleton_length(value: int32) {
    ensures list::length(List<int32>::Cons(value, List<int32>::Nil)) == Nat::Succ(Nat::Zero) by {
        unfold(list::length(List<int32>::Cons(value, List<int32>::Nil)));
        unfold(list::length(List<int32>::Nil));
        solve();
    }
}

verifying "stdlib_every_symbol.c";

theorem list_laws(xs: List<int32>, ys: List<int32>, zs: List<int32>, value: int32) {
    ensures list::contains(list::append(xs, ys), value)
        == if list::contains(xs, value) { true } else { list::contains(ys, value) } by {
        apply(list::contains_append(xs, ys, value));
    }
    ensures list::append(List<int32>::Nil, xs) == xs by {
        apply(list::append_left_identity(xs));
        assumption();
    }
    ensures list::append(xs, List<int32>::Nil) == xs by {
        apply(list::append_right_identity(xs));
        assumption();
    }
    ensures list::append(list::append(xs, ys), zs) == list::append(xs, list::append(ys, zs)) by {
        apply(list::append_associative(xs, ys, zs));
        assumption();
    }
    ensures list::contains(List<int32>::Nil, value) == false by {
        apply(list::contains_nil(value));
        assumption();
    }
    ensures list::contains(List<int32>::Cons(value, xs), value) by {
        apply(list::contains_cons(value, xs, value));
        solve();
    }
}

theorem pointer_lists(xs: List<int32*>, ys: List<int32*>, zs: List<int32*>, value: int32*) {
    ensures list::append(list::append(xs, ys), zs) == list::append(xs, list::append(ys, zs)) by {
        apply(list::append_associative(xs, ys, zs));
        assumption();
    }
}

theorem nested_lists(xs: List<List<int32>>) {
    ensures list::append(xs, List<List<int32>>::Nil) == xs by {
        apply(list::append_right_identity(xs));
        assumption();
    }
}
theorem append_constructor(head: int32, tail: List<int32>, ys: List<int32>) {
    ensures list::append(List<int32>::Cons(head, tail), ys)
        == List<int32>::Cons(head, list::append(tail, ys)) by {
        apply(list::append_cons(head, tail, ys));
    }
}

resource docs_allocation_wrapper(base: int32*, bytes: int32) {
    owns allocation(base, bytes);
}

theorem docs_use_int32_increment_upper_bound(value: int32, upper: int32) {
    requires value < upper;

    ensures to_integer(value + 1) <= to_integer(upper) by {
        apply(integer::int32_increment_upper_bound(value, upper));
    }
}

theorem docs_use_int32_increment_strictly_increases(value: int32, upper: int32) {
    requires value < upper;

    ensures to_integer(value) < to_integer(value + 1) by {
        apply(integer::int32_increment_strictly_increases(value, upper));
    }
}

theorem docs_use_int32_increment_lower_bound(value: int32, lower: int32, upper: int32) {
    requires lower <= value;
    requires value < upper;

    ensures to_integer(lower) <= to_integer(value + 1) by {
        apply(integer::int32_increment_lower_bound(value, lower, upper));
    }
}

theorem docs_use_int32_positive_is_nonnegative(value: int32) {
    requires 0 < value;

    ensures 0 <= value by {
        apply(integer::int32_positive_is_nonnegative(value));
    }
}

theorem docs_use_int32_increment_below_max_is_defined(value: int32) {
    requires value < 2147483647;

    ensures defined(value + 1) by {
        apply(integer::int32_increment_below_max_is_defined(value));
    }
}

theorem docs_use_int32_nonnegative_add_within_max_is_defined(value: int32, amount: int32) {
    requires 0 <= amount;
    requires to_integer(value) <= to_integer(2147483647 - amount);

    ensures defined(value + amount) by {
        apply(integer::int32_nonnegative_add_within_max_is_defined(value, amount));
    }
}

theorem docs_use_int32_nonnegative_subtract_within_value_is_defined(value: int32, amount: int32) {
    requires 0 <= amount;
    requires amount <= value;

    ensures defined(value - amount) by {
        apply(integer::int32_nonnegative_subtract_within_value_is_defined(value, amount));
    }
}

theorem docs_use_int32_positive_predecessor_is_nonnegative(value: int32) {
    requires 0 < value;

    ensures 0 <= to_integer(value - 1) by {
        apply(integer::int32_positive_predecessor_is_nonnegative(value));
    }
}

theorem docs_use_int32_positive_predecessor_strictly_decreases(value: int32) {
    requires 0 < value;

    ensures to_integer(value - 1) < to_integer(value) by {
        apply(integer::int32_positive_predecessor_strictly_decreases(value));
    }
}

theorem docs_use_uint32_positive_predecessor_strictly_decreases(value: uint32) {
    requires 0u32 < value;

    ensures to_integer(value - 1u32) < to_integer(value) by {
        apply(integer::uint32_positive_predecessor_strictly_decreases(value));
    }
}

theorem docs_use_uint32_increment_upper_bound(value: uint32, upper: uint32) {
    requires value < upper;

    ensures to_integer(value + 1u32) <= to_integer(upper) by {
        apply(integer::uint32_increment_upper_bound(value, upper));
    }
}

theorem docs_use_uint32_less_than_implies_positive_difference(value: uint32, upper: uint32) {
    requires value < upper;

    ensures 0 < to_integer(upper - value) by {
        apply(integer::uint32_less_than_implies_positive_difference(value, upper));
    }
}

theorem docs_use_uint32_difference_decreases_after_increment(value: uint32, bound: uint32) {
    requires value < bound;

    ensures integer::uint32_wrapping_add(integer::uint32_wrapping_sub(0u32, value), integer::uint32_wrapping_sub(bound, 1u32)) < integer::uint32_wrapping_add(integer::uint32_wrapping_sub(0u32, value), bound) by {
        apply(integer::uint32_difference_decreases_after_increment(value, bound));
        solve();
    }
}

theorem docs_use_uint64_less_than_less_equal_transitive(first: uint64, middle: uint64, last: uint64) {
    requires first < middle;
    requires middle <= last;

    ensures first < last by {
        apply(integer::uint64_less_than_less_equal_transitive(first, middle, last));
    }
}

theorem docs_use_uint64_less_equal_transitive(first: uint64, middle: uint64, last: uint64) {
    requires first <= middle;
    requires middle <= last;

    ensures first <= last by {
        apply(integer::uint64_less_equal_transitive(first, middle, last));
    }
}

theorem docs_use_int32_nonnegative_predecessor_upper_bound(value: int32, bound: int32) {
    requires 0 <= value;
    requires value <= bound;

    ensures to_integer(value - 1) <= to_integer(bound) by {
        apply(integer::int32_nonnegative_predecessor_upper_bound(value, bound));
    }
}

theorem docs_use_int32_less_equal_less_than_transitive(first: int32, middle: int32, last: int32) {
    requires first <= middle;
    requires middle < last;

    ensures first < last by {
        apply(integer::int32_less_equal_less_than_transitive(first, middle, last));
    }
}

theorem docs_use_int32_less_equal_transitive(first: int32, middle: int32, last: int32) {
    requires first <= middle;
    requires middle <= last;

    ensures first <= last by {
        apply(integer::int32_less_equal_transitive(first, middle, last));
    }
}

theorem docs_use_int32_less_equal_and_not_less_than_implies_equal(left: int32, right: int32) {
    requires left <= right;
    requires not (left < right);

    ensures left == right by {
        apply(integer::int32_less_equal_and_not_less_than_implies_equal(left, right));
    }
}

theorem docs_use_int32_less_equal_and_not_equal_implies_less_than(left: int32, right: int32) {
    requires left <= right;
    requires left != right;

    ensures left < right by {
        apply(integer::int32_less_equal_and_not_equal_implies_less_than(left, right));
    }
}

predicate docs_use_uint32_wrapping_add(left: uint32, right: uint32) {
    integer::uint32_wrapping_add(left, right) == integer::uint32_wrapping_add(left, right)
}

predicate docs_use_uint32_wrapping_sub(left: uint32, right: uint32) {
    integer::uint32_wrapping_sub(left, right) == integer::uint32_wrapping_sub(left, right)
}

predicate docs_use_uint32_wrapping_mul(left: uint32, right: uint32) {
    integer::uint32_wrapping_mul(left, right) == integer::uint32_wrapping_mul(left, right)
}

predicate docs_use_uint64_wrapping_add(left: uint64, right: uint64) {
    integer::uint64_wrapping_add(left, right) == integer::uint64_wrapping_add(left, right)
}

predicate docs_use_uint64_wrapping_sub(left: uint64, right: uint64) {
    integer::uint64_wrapping_sub(left, right) == integer::uint64_wrapping_sub(left, right)
}

predicate docs_use_uint64_wrapping_mul(left: uint64, right: uint64) {
    integer::uint64_wrapping_mul(left, right) == integer::uint64_wrapping_mul(left, right)
}

predicate docs_use_count(p: int32[], lo: int32, hi: int32, x: int32) {
    permutation::count(p, lo, hi, x) == permutation::count(p, lo, hi, x)
}

predicate docs_use_permutation(a: int32[], b: int32[], lo: int32, hi: int32) {
    permutation::permutation(a, b, lo, hi)
}

predicate docs_use_byte_count(bytes: uint8[], lo: int32, hi: int32, value: uint8) {
    bytes::count(bytes, lo, hi, value) == bytes::count(bytes, lo, hi, value)
}

predicate docs_use_bytes_equal(left: uint8[], left_lo: uint64, right: uint8[], right_lo: uint64, len: uint64) {
    bytes::equal(left, left_lo, right, right_lo, len)
}

predicate docs_use_bytes_equal_range(left: uint8[], right: uint8[], lo: uint64, hi: uint64) {
    bytes::equal_range(left, right, lo, hi)
}

predicate docs_use_bytes_all_equal(bytes: uint8[], lo: uint64, hi: uint64, value: uint8) {
    bytes::all_equal(bytes, lo, hi, value)
}

predicate docs_use_bytes_contains(bytes: uint8[], lo: uint64, hi: uint64, value: uint8) {
    bytes::contains(bytes, lo, hi, value)
}

predicate docs_use_bytes_all_not_equal(bytes: uint8[], lo: uint64, hi: uint64, value: uint8) {
    bytes::all_not_equal(bytes, lo, hi, value)
}

predicate docs_use_cstr_prefix(bytes: uint8[], len: uint64) {
    cstr::prefix(bytes, len)
}

predicate docs_use_cstr_len(bytes: uint8[], len: uint64) {
    cstr::len(bytes, len)
}

predicate docs_use_cstr(bytes: uint8[]) {
    cstr::cstr(bytes)
}

predicate docs_use_cstr_readable_len(bytes: uint8[], len: uint64) {
    cstr::readable_len(bytes, len)
}

theorem docs_use_cstr_readable_len_unique(bytes: uint8[], left: uint64, right: uint64) {
    requires forall (k: uint64) {
        k < left implies bytes[k] != '\0'
    };
    requires bytes[left] == '\0';
    requires forall (k: uint64) {
        k < right implies bytes[k] != '\0'
    };
    requires bytes[right] == '\0';

    ensures left == right by {
        apply(cstr::readable_len_unique(bytes, left, right));
    }
}

predicate docs_use_cstr_readable(bytes: uint8[]) {
    cstr::readable(bytes)
}

predicate docs_use_cstr_bounded(bytes: uint8[], max: uint64) {
    cstr::bounded(bytes, max)
}

theorem docs_use_cstr_len_has_prefix(bytes: uint8[], len: uint64) {
    requires cstr::len(bytes, len);

    ensures cstr::prefix(bytes, len) by {
        apply(cstr::len_has_prefix(bytes, len));
    }
}

theorem docs_use_cstr_len_has_terminator(bytes: uint8[], len: uint64) {
    requires cstr::len(bytes, len);

    ensures bytes[len] == '\0' by {
        apply(cstr::len_has_terminator(bytes, len));
    }
}

theorem docs_use_cstr_len_is_viewable(bytes: uint8[], len: uint64) {
    requires cstr::len(bytes, len);

    ensures viewable(bytes[0..len + 1u64]) by {
        apply(cstr::len_is_viewable(bytes, len));
    }
}
theorem use_integer_to_int8_round_trip(z: Integer) {
    requires z >= -128;
    requires z <= 127;
    ensures to_integer(to_int8(z)) == z by apply(integer::to_int8_round_trip(z));
}

theorem use_integer_to_int16_round_trip(z: Integer) {
    requires z >= -32768;
    requires z <= 32767;
    ensures to_integer(to_int16(z)) == z by apply(integer::to_int16_round_trip(z));
}

theorem use_integer_to_int32_round_trip(z: Integer) {
    requires z >= -2147483648;
    requires z <= 2147483647;
    ensures to_integer(to_int32(z)) == z by apply(integer::to_int32_round_trip(z));
}

theorem use_integer_to_uint8_round_trip(z: Integer) {
    requires z >= 0;
    requires z <= 255;
    ensures to_integer(to_uint8(z)) == z by apply(integer::to_uint8_round_trip(z));
}

theorem use_integer_to_uint16_round_trip(z: Integer) {
    requires z >= 0;
    requires z <= 65535;
    ensures to_integer(to_uint16(z)) == z by apply(integer::to_uint16_round_trip(z));
}

theorem use_integer_to_uint32_round_trip(z: Integer) {
    requires z >= 0;
    requires z <= 4294967295;
    ensures to_integer(to_uint32(z)) == z by apply(integer::to_uint32_round_trip(z));
}

theorem use_integer_to_int64_round_trip(z: Integer) {
    requires z >= -9223372036854775808;
    requires z <= 9223372036854775807;
    ensures to_integer(to_int64(z)) == z by apply(integer::to_int64_round_trip(z));
}

theorem use_integer_to_uint64_round_trip(z: Integer) {
    requires z >= 0;
    requires z <= 18446744073709551615;
    ensures to_integer(to_uint64(z)) == z by apply(integer::to_uint64_round_trip(z));
}

theorem use_scaled_quotient(n: Integer, d: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires bound * d <= n;
    requires n <= bound * d;
    ensures bound <= truncating_quotient(n, d) by apply(integer::positive_divisor_quotient_lower(n, d, bound));
    ensures truncating_quotient(n, d) <= bound by apply(integer::positive_divisor_quotient_upper(n, d, bound));
}

theorem use_strict_lower(n: Integer, d: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires bound < 0;
    requires bound * d < n;
    ensures bound < truncating_quotient(n, d) by apply(integer::positive_divisor_quotient_strict_lower(n, d, bound));
}

theorem use_strict_upper(n: Integer, d: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires 0 < bound;
    requires n < bound * d;
    ensures truncating_quotient(n, d) < bound by apply(integer::positive_divisor_quotient_strict_upper(n, d, bound));
}

theorem use_lower_correction_bound(n: Integer, d: Integer, q: Integer, r: Integer, bound: Integer) {
    requires bound <= q; requires bound * d <= n;
    requires n == q * d + r;
    requires r < 0;
    ensures bound + 1 <= q by apply(integer::lower_correction_bound(n, d, q, r, bound));
}
theorem use_upper_correction_bound(n: Integer, d: Integer, q: Integer, r: Integer, bound: Integer) {
    requires q <= bound; requires n <= bound * d;
    requires n == q * d + r;
    requires 0 < r;
    ensures q <= bound + -1 by apply(integer::upper_correction_bound(n, d, q, r, bound));
}

theorem use_multiply_orders(a: Integer, b: Integer, c: Integer) {
 requires a <= b; requires 0 <= c;
 ensures a * c <= b * c by apply(integer::multiply_order_nonnegative(a, b, c));
}
theorem use_reverse_multiply_order(a: Integer, b: Integer, c: Integer) {
 requires a <= b; requires c <= 0;
 ensures b * c <= a * c by apply(integer::multiply_order_nonpositive(a, b, c));
}
theorem use_scaled_product(value: Integer, amount: Integer, size: Integer, lower: Integer, upper: Integer) {
 requires lower <= value; requires value <= upper;
 requires lower <= 0; requires 0 <= upper;
 requires 0 <= amount; requires amount <= size;
 ensures lower * size <= value * amount by apply(integer::scaled_product_bounds(value, amount, size, lower, upper));
 ensures value * amount <= upper * size by apply(integer::scaled_product_bounds(value, amount, size, lower, upper));
}

theorem use_int32_remainder_to_integer(left: int32, right: int32) {
    requires defined(left % right);
    requires to_integer(right) != 0;
    ensures to_integer(left % right) == truncating_remainder(to_integer(left), to_integer(right)) by {
        apply(integer::int32_remainder_to_integer(left, right));
    }
}


theorem use_format_pow10_0() {
    ensures format::pow10(0u64) == 1u64 by apply(format::pow10_0());
}

theorem use_format_pow10_1() {
    ensures format::pow10(1u64) == 10u64 by apply(format::pow10_1());
}

theorem use_format_pow10_2() {
    ensures format::pow10(2u64) == 100u64 by apply(format::pow10_2());
}

theorem use_format_pow10_3() {
    ensures format::pow10(3u64) == 1000u64 by apply(format::pow10_3());
}

theorem use_format_pow10_4() {
    ensures format::pow10(4u64) == 10000u64 by apply(format::pow10_4());
}

theorem use_format_pow10_5() {
    ensures format::pow10(5u64) == 100000u64 by apply(format::pow10_5());
}

theorem use_format_pow10_6() {
    ensures format::pow10(6u64) == 1000000u64 by apply(format::pow10_6());
}

theorem use_format_pow10_7() {
    ensures format::pow10(7u64) == 10000000u64 by apply(format::pow10_7());
}

theorem use_format_pow10_8() {
    ensures format::pow10(8u64) == 100000000u64 by apply(format::pow10_8());
}

theorem use_format_pow10_9() {
    ensures format::pow10(9u64) == 1000000000u64 by apply(format::pow10_9());
}

theorem use_format_decimal_length_1(v: uint64) {
    requires v < 10u64;
    ensures format::decimal_length(v) == 1u64 by apply(format::decimal_length_1(v));
}

theorem use_format_decimal_length_2(v: uint64) {
    requires 10u64 <= v;
    requires v < 100u64;
    ensures format::decimal_length(v) == 2u64 by apply(format::decimal_length_2(v));
}

theorem use_format_decimal_length_3(v: uint64) {
    requires 100u64 <= v;
    requires v < 1000u64;
    ensures format::decimal_length(v) == 3u64 by apply(format::decimal_length_3(v));
}

theorem use_format_decimal_length_4(v: uint64) {
    requires 1000u64 <= v;
    requires v < 10000u64;
    ensures format::decimal_length(v) == 4u64 by apply(format::decimal_length_4(v));
}

theorem use_format_decimal_length_5(v: uint64) {
    requires 10000u64 <= v;
    requires v < 100000u64;
    ensures format::decimal_length(v) == 5u64 by apply(format::decimal_length_5(v));
}

theorem use_format_decimal_length_6(v: uint64) {
    requires 100000u64 <= v;
    requires v < 1000000u64;
    ensures format::decimal_length(v) == 6u64 by apply(format::decimal_length_6(v));
}

theorem use_format_decimal_length_7(v: uint64) {
    requires 1000000u64 <= v;
    requires v < 10000000u64;
    ensures format::decimal_length(v) == 7u64 by apply(format::decimal_length_7(v));
}

theorem use_format_decimal_length_8(v: uint64) {
    requires 10000000u64 <= v;
    requires v < 100000000u64;
    ensures format::decimal_length(v) == 8u64 by apply(format::decimal_length_8(v));
}

theorem use_format_decimal_length_9(v: uint64) {
    requires 100000000u64 <= v;
    requires v < 1000000000u64;
    ensures format::decimal_length(v) == 9u64 by apply(format::decimal_length_9(v));
}

theorem use_format_decimal_length_10(v: uint64) {
    requires 1000000000u64 <= v;
    requires v < 10000000000u64;
    ensures format::decimal_length(v) == 10u64 by apply(format::decimal_length_10(v));
}

theorem use_format_decimal_digit_of_length(v: uint64) {
    requires format::decimal_length(v) == 2u64;
    ensures format::decimal_digit(v, 1u64) == (48u64 + v / format::pow10(2u64 - 1u64 - 1u64) % 10u64) as uint8 by
        apply(format::decimal_digit_of_length(v, 2u64, 1u64));
}

theorem use_format_decimal_digit_lower_bound(v: uint64) {
    ensures 48u8 <= format::decimal_digit(v, 0u64) by apply(format::decimal_digit_lower_bound(v, 0u64));
}

theorem use_format_padded_digit_lower_bound(v: uint64) {
    ensures 48u8 <= format::padded_digit(v, 3u64, 48u8, 1u64) by apply(format::padded_digit_lower_bound(v, 3u64, 1u64));
}

theorem use_format_padded_digit(v: uint64) {
    requires format::padded_length(v, 3u64) == 3u64;
    requires format::decimal_length(v) == 1u64;
    ensures format::padded_digit(v, 3u64, 48u8, 0u64) == 48u8 by {
        unfold(format::padded_digit(v, 3u64, 48u8, 0u64));
        solve();
    }
}

theorem use_format_signed_digit() {
    ensures format::signed_digit(-5, 0u64) == 45u8 by {
        unfold(format::signed_digit(-5, 0u64));
        solve();
    }
}

theorem use_format_signed_length(v: int32) {
    requires 0 <= v;
    ensures format::signed_length(v) == format::decimal_length(format::magnitude(v)) by {
        unfold(format::signed_length(v));
        solve();
    }
}
theorem use_rust_i8_min() {
    ensures i8::min((127i64 as int8), (-128i64 as int8)) == (-128i64 as int8) by {
        unfold(i8::min((127i64 as int8), (-128i64 as int8)));
        solve();
    }
}

theorem use_rust_i8_max() {
    ensures i8::max((127i64 as int8), (-128i64 as int8)) == (127i64 as int8) by {
        unfold(i8::max((127i64 as int8), (-128i64 as int8)));
        solve();
    }
}

theorem use_rust_i8_wrapping_add() {
    ensures i8::wrapping_add((127i64 as int8), (1i64 as int8)) == (-128i64 as int8) by {
        unfold(i8::wrapping_add((127i64 as int8), (1i64 as int8)));
        solve();
    }
}

theorem use_rust_i8_wrapping_sub() {
    ensures i8::wrapping_sub((-128i64 as int8), (1i64 as int8)) == (127i64 as int8) by {
        unfold(i8::wrapping_sub((-128i64 as int8), (1i64 as int8)));
        solve();
    }
}

theorem use_rust_i8_wrapping_mul() {
    ensures i8::wrapping_mul((127i64 as int8), (2i64 as int8)) == (-2i64 as int8) by {
        unfold(i8::wrapping_mul((127i64 as int8), (2i64 as int8)));
        solve();
    }
}

theorem use_rust_i8_saturating_add() {
    ensures i8::saturating_add((127i64 as int8), (1i64 as int8)) == (127i64 as int8) by {
        unfold(i8::saturating_add((127i64 as int8), (1i64 as int8)));
        solve();
    }
}

theorem use_rust_i8_saturating_sub() {
    ensures i8::saturating_sub((-128i64 as int8), (1i64 as int8)) == (-128i64 as int8) by {
        unfold(i8::saturating_sub((-128i64 as int8), (1i64 as int8)));
        solve();
    }
}

theorem use_rust_i8_checked_add() {
    ensures i8::checked_add((127i64 as int8), (1i64 as int8)) == Option<int8>::None by {
        unfold(i8::checked_add((127i64 as int8), (1i64 as int8)));
        solve();
    }
}

theorem use_rust_i8_checked_sub() {
    ensures i8::checked_sub((-128i64 as int8), (1i64 as int8)) == Option<int8>::None by {
        unfold(i8::checked_sub((-128i64 as int8), (1i64 as int8)));
        solve();
    }
}

theorem use_rust_i8_abs_diff() {
    ensures i8::abs_diff((-128i64 as int8), (127i64 as int8)) == (255u32 as uint8) by {
        unfold(i8::abs_diff((-128i64 as int8), (127i64 as int8)));
        solve();
    }
}

theorem use_rust_i8_unsigned_abs() {
    ensures i8::unsigned_abs((-128i64 as int8)) == (128u32 as uint8) by {
        unfold(i8::unsigned_abs((-128i64 as int8)));
        solve();
    }
}

theorem use_rust_i16_min() {
    ensures i16::min((32767i64 as int16), (-32768i64 as int16)) == (-32768i64 as int16) by {
        unfold(i16::min((32767i64 as int16), (-32768i64 as int16)));
        solve();
    }
}

theorem use_rust_i16_max() {
    ensures i16::max((32767i64 as int16), (-32768i64 as int16)) == (32767i64 as int16) by {
        unfold(i16::max((32767i64 as int16), (-32768i64 as int16)));
        solve();
    }
}

theorem use_rust_i16_wrapping_add() {
    ensures i16::wrapping_add((32767i64 as int16), (1i64 as int16)) == (-32768i64 as int16) by {
        unfold(i16::wrapping_add((32767i64 as int16), (1i64 as int16)));
        solve();
    }
}

theorem use_rust_i16_wrapping_sub() {
    ensures i16::wrapping_sub((-32768i64 as int16), (1i64 as int16)) == (32767i64 as int16) by {
        unfold(i16::wrapping_sub((-32768i64 as int16), (1i64 as int16)));
        solve();
    }
}

theorem use_rust_i16_wrapping_mul() {
    ensures i16::wrapping_mul((32767i64 as int16), (2i64 as int16)) == (-2i64 as int16) by {
        unfold(i16::wrapping_mul((32767i64 as int16), (2i64 as int16)));
        solve();
    }
}

theorem use_rust_i16_saturating_add() {
    ensures i16::saturating_add((32767i64 as int16), (1i64 as int16)) == (32767i64 as int16) by {
        unfold(i16::saturating_add((32767i64 as int16), (1i64 as int16)));
        solve();
    }
}

theorem use_rust_i16_saturating_sub() {
    ensures i16::saturating_sub((-32768i64 as int16), (1i64 as int16)) == (-32768i64 as int16) by {
        unfold(i16::saturating_sub((-32768i64 as int16), (1i64 as int16)));
        solve();
    }
}

theorem use_rust_i16_checked_add() {
    ensures i16::checked_add((32767i64 as int16), (1i64 as int16)) == Option<int16>::None by {
        unfold(i16::checked_add((32767i64 as int16), (1i64 as int16)));
        solve();
    }
}

theorem use_rust_i16_checked_sub() {
    ensures i16::checked_sub((-32768i64 as int16), (1i64 as int16)) == Option<int16>::None by {
        unfold(i16::checked_sub((-32768i64 as int16), (1i64 as int16)));
        solve();
    }
}

theorem use_rust_i16_abs_diff() {
    ensures i16::abs_diff((-32768i64 as int16), (32767i64 as int16)) == (65535u32 as uint16) by {
        unfold(i16::abs_diff((-32768i64 as int16), (32767i64 as int16)));
        solve();
    }
}

theorem use_rust_i16_unsigned_abs() {
    ensures i16::unsigned_abs((-32768i64 as int16)) == (32768u32 as uint16) by {
        unfold(i16::unsigned_abs((-32768i64 as int16)));
        solve();
    }
}

theorem use_rust_i32_min() {
    ensures i32::min(2147483647, (-2147483648i64 as int32)) == (-2147483648i64 as int32) by {
        unfold(i32::min(2147483647, (-2147483648i64 as int32)));
        solve();
    }
}

theorem use_rust_i32_max() {
    ensures i32::max(2147483647, (-2147483648i64 as int32)) == 2147483647 by {
        unfold(i32::max(2147483647, (-2147483648i64 as int32)));
        solve();
    }
}

theorem use_rust_i32_wrapping_add() {
    ensures i32::wrapping_add(2147483647, 1) == (-2147483648i64 as int32) by {
        unfold(i32::wrapping_add(2147483647, 1));
        solve();
    }
}

theorem use_rust_i32_wrapping_sub() {
    ensures i32::wrapping_sub((-2147483648i64 as int32), 1) == 2147483647 by {
        unfold(i32::wrapping_sub((-2147483648i64 as int32), 1));
        solve();
    }
}

theorem use_rust_i32_wrapping_mul() {
    ensures i32::wrapping_mul(2147483647, 2) == (-2i64 as int32) by {
        unfold(i32::wrapping_mul(2147483647, 2));
        solve();
    }
}

theorem use_rust_i32_saturating_add() {
    ensures i32::saturating_add(2147483647, 1) == 2147483647 by {
        unfold(i32::saturating_add(2147483647, 1));
        solve();
    }
}

theorem use_rust_i32_saturating_sub() {
    ensures i32::saturating_sub((-2147483648i64 as int32), 1) == (-2147483648i64 as int32) by {
        unfold(i32::saturating_sub((-2147483648i64 as int32), 1));
        solve();
    }
}

theorem use_rust_i32_checked_add() {
    ensures i32::checked_add(2147483647, 1) == Option<int32>::None by {
        unfold(i32::checked_add(2147483647, 1));
        solve();
    }
}

theorem use_rust_i32_checked_sub() {
    ensures i32::checked_sub((-2147483648i64 as int32), 1) == Option<int32>::None by {
        unfold(i32::checked_sub((-2147483648i64 as int32), 1));
        solve();
    }
}

theorem use_rust_i32_abs_diff() {
    ensures i32::abs_diff((-2147483648i64 as int32), 2147483647) == 4294967295u32 by {
        unfold(i32::abs_diff((-2147483648i64 as int32), 2147483647));
        solve();
    }
}

theorem use_rust_i32_unsigned_abs() {
    ensures i32::unsigned_abs((-2147483648i64 as int32)) == 2147483648u32 by {
        unfold(i32::unsigned_abs((-2147483648i64 as int32)));
        solve();
    }
}

theorem use_rust_i64_min() {
    ensures i64::min(9223372036854775807i64, -9223372036854775808i64) == -9223372036854775808i64 by {
        unfold(i64::min(9223372036854775807i64, -9223372036854775808i64));
        solve();
    }
}

theorem use_rust_i64_max() {
    ensures i64::max(9223372036854775807i64, -9223372036854775808i64) == 9223372036854775807i64 by {
        unfold(i64::max(9223372036854775807i64, -9223372036854775808i64));
        solve();
    }
}

theorem use_rust_i64_wrapping_add() {
    ensures i64::wrapping_add(9223372036854775807i64, 1i64) == -9223372036854775808i64 by {
        unfold(i64::wrapping_add(9223372036854775807i64, 1i64));
        solve();
    }
}

theorem use_rust_i64_wrapping_sub() {
    ensures i64::wrapping_sub(-9223372036854775808i64, 1i64) == 9223372036854775807i64 by {
        unfold(i64::wrapping_sub(-9223372036854775808i64, 1i64));
        solve();
    }
}

theorem use_rust_i64_wrapping_mul() {
    ensures i64::wrapping_mul(9223372036854775807i64, 2i64) == -2i64 by {
        unfold(i64::wrapping_mul(9223372036854775807i64, 2i64));
        solve();
    }
}

theorem use_rust_i64_saturating_add() {
    ensures i64::saturating_add(9223372036854775807i64, 1i64) == 9223372036854775807i64 by {
        unfold(i64::saturating_add(9223372036854775807i64, 1i64));
        solve();
    }
}

theorem use_rust_i64_saturating_sub() {
    ensures i64::saturating_sub(-9223372036854775808i64, 1i64) == -9223372036854775808i64 by {
        unfold(i64::saturating_sub(-9223372036854775808i64, 1i64));
        solve();
    }
}

theorem use_rust_i64_checked_add() {
    ensures i64::checked_add(9223372036854775807i64, 1i64) == Option<int64>::None by {
        unfold(i64::checked_add(9223372036854775807i64, 1i64));
        solve();
    }
}

theorem use_rust_i64_checked_sub() {
    ensures i64::checked_sub(-9223372036854775808i64, 1i64) == Option<int64>::None by {
        unfold(i64::checked_sub(-9223372036854775808i64, 1i64));
        solve();
    }
}

theorem use_rust_i64_abs_diff() {
    ensures i64::abs_diff(-9223372036854775808i64, 9223372036854775807i64) == 18446744073709551615u64 by {
        unfold(i64::abs_diff(-9223372036854775808i64, 9223372036854775807i64));
        solve();
    }
}

theorem use_rust_i64_unsigned_abs() {
    ensures i64::unsigned_abs(-9223372036854775808i64) == 9223372036854775808u64 by {
        unfold(i64::unsigned_abs(-9223372036854775808i64));
        solve();
    }
}

theorem use_rust_isize_min() {
    ensures isize::min(9223372036854775807i64, -9223372036854775808i64) == -9223372036854775808i64 by {
        unfold(isize::min(9223372036854775807i64, -9223372036854775808i64));
        solve();
    }
}

theorem use_rust_isize_max() {
    ensures isize::max(9223372036854775807i64, -9223372036854775808i64) == 9223372036854775807i64 by {
        unfold(isize::max(9223372036854775807i64, -9223372036854775808i64));
        solve();
    }
}

theorem use_rust_isize_wrapping_add() {
    ensures isize::wrapping_add(9223372036854775807i64, 1i64) == -9223372036854775808i64 by {
        unfold(isize::wrapping_add(9223372036854775807i64, 1i64));
        solve();
    }
}

theorem use_rust_isize_wrapping_sub() {
    ensures isize::wrapping_sub(-9223372036854775808i64, 1i64) == 9223372036854775807i64 by {
        unfold(isize::wrapping_sub(-9223372036854775808i64, 1i64));
        solve();
    }
}

theorem use_rust_isize_wrapping_mul() {
    ensures isize::wrapping_mul(9223372036854775807i64, 2i64) == -2i64 by {
        unfold(isize::wrapping_mul(9223372036854775807i64, 2i64));
        solve();
    }
}

theorem use_rust_isize_saturating_add() {
    ensures isize::saturating_add(9223372036854775807i64, 1i64) == 9223372036854775807i64 by {
        unfold(isize::saturating_add(9223372036854775807i64, 1i64));
        solve();
    }
}

theorem use_rust_isize_saturating_sub() {
    ensures isize::saturating_sub(-9223372036854775808i64, 1i64) == -9223372036854775808i64 by {
        unfold(isize::saturating_sub(-9223372036854775808i64, 1i64));
        solve();
    }
}

theorem use_rust_isize_checked_add() {
    ensures isize::checked_add(9223372036854775807i64, 1i64) == Option<int64>::None by {
        unfold(isize::checked_add(9223372036854775807i64, 1i64));
        solve();
    }
}

theorem use_rust_isize_checked_sub() {
    ensures isize::checked_sub(-9223372036854775808i64, 1i64) == Option<int64>::None by {
        unfold(isize::checked_sub(-9223372036854775808i64, 1i64));
        solve();
    }
}

theorem use_rust_isize_abs_diff() {
    ensures isize::abs_diff(-9223372036854775808i64, 9223372036854775807i64) == 18446744073709551615u64 by {
        unfold(isize::abs_diff(-9223372036854775808i64, 9223372036854775807i64));
        solve();
    }
}

theorem use_rust_isize_unsigned_abs() {
    ensures isize::unsigned_abs(-9223372036854775808i64) == 9223372036854775808u64 by {
        unfold(isize::unsigned_abs(-9223372036854775808i64));
        solve();
    }
}

theorem use_rust_u8_min() {
    ensures u8::min((255u32 as uint8), (0u32 as uint8)) == (0u32 as uint8) by {
        unfold(u8::min((255u32 as uint8), (0u32 as uint8)));
        solve();
    }
}

theorem use_rust_u8_max() {
    ensures u8::max((255u32 as uint8), (0u32 as uint8)) == (255u32 as uint8) by {
        unfold(u8::max((255u32 as uint8), (0u32 as uint8)));
        solve();
    }
}

theorem use_rust_u8_wrapping_add() {
    ensures u8::wrapping_add((255u32 as uint8), (1u32 as uint8)) == (0u32 as uint8) by {
        unfold(u8::wrapping_add((255u32 as uint8), (1u32 as uint8)));
        solve();
    }
}

theorem use_rust_u8_wrapping_sub() {
    ensures u8::wrapping_sub((0u32 as uint8), (1u32 as uint8)) == (255u32 as uint8) by {
        unfold(u8::wrapping_sub((0u32 as uint8), (1u32 as uint8)));
        solve();
    }
}

theorem use_rust_u8_wrapping_mul() {
    ensures u8::wrapping_mul((255u32 as uint8), (2u32 as uint8)) == (254u32 as uint8) by {
        unfold(u8::wrapping_mul((255u32 as uint8), (2u32 as uint8)));
        solve();
    }
}

theorem use_rust_u8_saturating_add() {
    ensures u8::saturating_add((255u32 as uint8), (1u32 as uint8)) == (255u32 as uint8) by {
        unfold(u8::saturating_add((255u32 as uint8), (1u32 as uint8)));
        solve();
    }
}

theorem use_rust_u8_saturating_sub() {
    ensures u8::saturating_sub((0u32 as uint8), (1u32 as uint8)) == (0u32 as uint8) by {
        unfold(u8::saturating_sub((0u32 as uint8), (1u32 as uint8)));
        solve();
    }
}

theorem use_rust_u8_checked_add() {
    ensures u8::checked_add((255u32 as uint8), (1u32 as uint8)) == Option<uint8>::None by {
        unfold(u8::checked_add((255u32 as uint8), (1u32 as uint8)));
        solve();
    }
}

theorem use_rust_u8_checked_sub() {
    ensures u8::checked_sub((0u32 as uint8), (1u32 as uint8)) == Option<uint8>::None by {
        unfold(u8::checked_sub((0u32 as uint8), (1u32 as uint8)));
        solve();
    }
}

theorem use_rust_u8_abs_diff() {
    ensures u8::abs_diff((0u32 as uint8), (255u32 as uint8)) == (255u32 as uint8) by {
        unfold(u8::abs_diff((0u32 as uint8), (255u32 as uint8)));
        solve();
    }
}

theorem use_rust_u16_min() {
    ensures u16::min((65535u32 as uint16), (0u32 as uint16)) == (0u32 as uint16) by {
        unfold(u16::min((65535u32 as uint16), (0u32 as uint16)));
        solve();
    }
}

theorem use_rust_u16_max() {
    ensures u16::max((65535u32 as uint16), (0u32 as uint16)) == (65535u32 as uint16) by {
        unfold(u16::max((65535u32 as uint16), (0u32 as uint16)));
        solve();
    }
}

theorem use_rust_u16_wrapping_add() {
    ensures u16::wrapping_add((65535u32 as uint16), (1u32 as uint16)) == (0u32 as uint16) by {
        unfold(u16::wrapping_add((65535u32 as uint16), (1u32 as uint16)));
        solve();
    }
}

theorem use_rust_u16_wrapping_sub() {
    ensures u16::wrapping_sub((0u32 as uint16), (1u32 as uint16)) == (65535u32 as uint16) by {
        unfold(u16::wrapping_sub((0u32 as uint16), (1u32 as uint16)));
        solve();
    }
}

theorem use_rust_u16_wrapping_mul() {
    ensures u16::wrapping_mul((65535u32 as uint16), (2u32 as uint16)) == (65534u32 as uint16) by {
        unfold(u16::wrapping_mul((65535u32 as uint16), (2u32 as uint16)));
        solve();
    }
}

theorem use_rust_u16_saturating_add() {
    ensures u16::saturating_add((65535u32 as uint16), (1u32 as uint16)) == (65535u32 as uint16) by {
        unfold(u16::saturating_add((65535u32 as uint16), (1u32 as uint16)));
        solve();
    }
}

theorem use_rust_u16_saturating_sub() {
    ensures u16::saturating_sub((0u32 as uint16), (1u32 as uint16)) == (0u32 as uint16) by {
        unfold(u16::saturating_sub((0u32 as uint16), (1u32 as uint16)));
        solve();
    }
}

theorem use_rust_u16_checked_add() {
    ensures u16::checked_add((65535u32 as uint16), (1u32 as uint16)) == Option<uint16>::None by {
        unfold(u16::checked_add((65535u32 as uint16), (1u32 as uint16)));
        solve();
    }
}

theorem use_rust_u16_checked_sub() {
    ensures u16::checked_sub((0u32 as uint16), (1u32 as uint16)) == Option<uint16>::None by {
        unfold(u16::checked_sub((0u32 as uint16), (1u32 as uint16)));
        solve();
    }
}

theorem use_rust_u16_abs_diff() {
    ensures u16::abs_diff((0u32 as uint16), (65535u32 as uint16)) == (65535u32 as uint16) by {
        unfold(u16::abs_diff((0u32 as uint16), (65535u32 as uint16)));
        solve();
    }
}

theorem use_rust_u32_min() {
    ensures u32::min(4294967295u32, 0u32) == 0u32 by {
        unfold(u32::min(4294967295u32, 0u32));
        solve();
    }
}

theorem use_rust_u32_max() {
    ensures u32::max(4294967295u32, 0u32) == 4294967295u32 by {
        unfold(u32::max(4294967295u32, 0u32));
        solve();
    }
}

theorem use_rust_u32_wrapping_add() {
    ensures u32::wrapping_add(4294967295u32, 1u32) == 0u32 by {
        unfold(u32::wrapping_add(4294967295u32, 1u32));
        solve();
    }
}

theorem use_rust_u32_wrapping_sub() {
    ensures u32::wrapping_sub(0u32, 1u32) == 4294967295u32 by {
        unfold(u32::wrapping_sub(0u32, 1u32));
        solve();
    }
}

theorem use_rust_u32_wrapping_mul() {
    ensures u32::wrapping_mul(4294967295u32, 2u32) == 4294967294u32 by {
        unfold(u32::wrapping_mul(4294967295u32, 2u32));
        solve();
    }
}

theorem use_rust_u32_saturating_add() {
    ensures u32::saturating_add(4294967295u32, 1u32) == 4294967295u32 by {
        unfold(u32::saturating_add(4294967295u32, 1u32));
        solve();
    }
}

theorem use_rust_u32_saturating_sub() {
    ensures u32::saturating_sub(0u32, 1u32) == 0u32 by {
        unfold(u32::saturating_sub(0u32, 1u32));
        solve();
    }
}

theorem use_rust_u32_checked_add() {
    ensures u32::checked_add(4294967295u32, 1u32) == Option<uint32>::None by {
        unfold(u32::checked_add(4294967295u32, 1u32));
        solve();
    }
}

theorem use_rust_u32_checked_sub() {
    ensures u32::checked_sub(0u32, 1u32) == Option<uint32>::None by {
        unfold(u32::checked_sub(0u32, 1u32));
        solve();
    }
}

theorem use_rust_u32_abs_diff() {
    ensures u32::abs_diff(0u32, 4294967295u32) == 4294967295u32 by {
        unfold(u32::abs_diff(0u32, 4294967295u32));
        solve();
    }
}

theorem use_rust_u64_min() {
    ensures u64::min(18446744073709551615u64, 0u64) == 0u64 by {
        unfold(u64::min(18446744073709551615u64, 0u64));
        solve();
    }
}

theorem use_rust_u64_max() {
    ensures u64::max(18446744073709551615u64, 0u64) == 18446744073709551615u64 by {
        unfold(u64::max(18446744073709551615u64, 0u64));
        solve();
    }
}

theorem use_rust_u64_wrapping_add() {
    ensures u64::wrapping_add(18446744073709551615u64, 1u64) == 0u64 by {
        unfold(u64::wrapping_add(18446744073709551615u64, 1u64));
        solve();
    }
}

theorem use_rust_u64_wrapping_sub() {
    ensures u64::wrapping_sub(0u64, 1u64) == 18446744073709551615u64 by {
        unfold(u64::wrapping_sub(0u64, 1u64));
        solve();
    }
}

theorem use_rust_u64_wrapping_mul() {
    ensures u64::wrapping_mul(18446744073709551615u64, 2u64) == 18446744073709551614u64 by {
        unfold(u64::wrapping_mul(18446744073709551615u64, 2u64));
        solve();
    }
}

theorem use_rust_u64_saturating_add() {
    ensures u64::saturating_add(18446744073709551615u64, 1u64) == 18446744073709551615u64 by {
        unfold(u64::saturating_add(18446744073709551615u64, 1u64));
        solve();
    }
}

theorem use_rust_u64_saturating_sub() {
    ensures u64::saturating_sub(0u64, 1u64) == 0u64 by {
        unfold(u64::saturating_sub(0u64, 1u64));
        solve();
    }
}

theorem use_rust_u64_checked_add() {
    ensures u64::checked_add(18446744073709551615u64, 1u64) == Option<uint64>::None by {
        unfold(u64::checked_add(18446744073709551615u64, 1u64));
        solve();
    }
}

theorem use_rust_u64_checked_sub() {
    ensures u64::checked_sub(0u64, 1u64) == Option<uint64>::None by {
        unfold(u64::checked_sub(0u64, 1u64));
        solve();
    }
}

theorem use_rust_u64_abs_diff() {
    ensures u64::abs_diff(0u64, 18446744073709551615u64) == 18446744073709551615u64 by {
        unfold(u64::abs_diff(0u64, 18446744073709551615u64));
        solve();
    }
}

theorem use_rust_usize_min() {
    ensures usize::min(18446744073709551615u64, 0u64) == 0u64 by {
        unfold(usize::min(18446744073709551615u64, 0u64));
        solve();
    }
}

theorem use_rust_usize_max() {
    ensures usize::max(18446744073709551615u64, 0u64) == 18446744073709551615u64 by {
        unfold(usize::max(18446744073709551615u64, 0u64));
        solve();
    }
}

theorem use_rust_usize_wrapping_add() {
    ensures usize::wrapping_add(18446744073709551615u64, 1u64) == 0u64 by {
        unfold(usize::wrapping_add(18446744073709551615u64, 1u64));
        solve();
    }
}

theorem use_rust_usize_wrapping_sub() {
    ensures usize::wrapping_sub(0u64, 1u64) == 18446744073709551615u64 by {
        unfold(usize::wrapping_sub(0u64, 1u64));
        solve();
    }
}

theorem use_rust_usize_wrapping_mul() {
    ensures usize::wrapping_mul(18446744073709551615u64, 2u64) == 18446744073709551614u64 by {
        unfold(usize::wrapping_mul(18446744073709551615u64, 2u64));
        solve();
    }
}

theorem use_rust_usize_saturating_add() {
    ensures usize::saturating_add(18446744073709551615u64, 1u64) == 18446744073709551615u64 by {
        unfold(usize::saturating_add(18446744073709551615u64, 1u64));
        solve();
    }
}

theorem use_rust_usize_saturating_sub() {
    ensures usize::saturating_sub(0u64, 1u64) == 0u64 by {
        unfold(usize::saturating_sub(0u64, 1u64));
        solve();
    }
}

theorem use_rust_usize_checked_add() {
    ensures usize::checked_add(18446744073709551615u64, 1u64) == Option<uint64>::None by {
        unfold(usize::checked_add(18446744073709551615u64, 1u64));
        solve();
    }
}

theorem use_rust_usize_checked_sub() {
    ensures usize::checked_sub(0u64, 1u64) == Option<uint64>::None by {
        unfold(usize::checked_sub(0u64, 1u64));
        solve();
    }
}

theorem use_rust_usize_abs_diff() {
    ensures usize::abs_diff(0u64, 18446744073709551615u64) == 18446744073709551615u64 by {
        unfold(usize::abs_diff(0u64, 18446744073709551615u64));
        solve();
    }
}

theorem use_option_unwrap_or(d: int32) {
    ensures option::unwrap_or(Option<int32>::None, d) == d by {
        unfold(option::unwrap_or(Option<int32>::None, d));
        solve();
    }
}
```

```expect
pass
```
