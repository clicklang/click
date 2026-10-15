# A call requirement with a false antecedent stays unresolved

Soundness: incomplete. A true call precondition is refused, and nothing false
is accepted.

The axiomatic `std::span<T>::subspan` contract
(`src/languages/cpp/standard_library.rs`) requires:

```click
requires {p2} != {dynamic_extent} implies {p2} <= std_span_size(this) - {p1};
```

A call that passes `std::dynamic_extent` as the count, such as
`s.subspan(1)` with its defaulted count, makes the antecedent
`18446744073709551615u64 != 18446744073709551615u64`, which is false. The
call still stops with that implication open:

```text
`probe.contract` tactic 0: `execute()` could not verify C operation: call
cannot finish with unresolved proof obligations:
  context: span__int__value_unsigned_long_18446744073709551615_subspan precondition
  callee: span__int__value_unsigned_long_18446744073709551615_subspan; source contract input clause 4
  pending goal: false implies 18446744073709551615u64 <= at(<state A>, std_span_size(s)) - 1u64
  C operation: @click:result = span__int__value_unsigned_long_18446744073709551615_subspan(&s, ((uint64)1), 18446744073709551615u64)
```

The pending goal is an implication whose antecedent has already reduced to
`false`, so it holds trivially.

Three nightly tests in `tests/bitcoin_core_money_range.rs` fail this way:
`defaulted_span_arguments_import_as_compiler_constants`,
`axiomatic_span_byte_element_entries_verify` and
`axiomatic_span_dynamic_extent_requirement_is_proved_before_view_recovery`.

```sh
CLICK_NIGHTLY=1 RUST_MIN_STACK=8388608 \
CLICK_CPP_EXPORTER="$(scripts/build-cpp-exporter.sh)" \
cargo nextest run --test bitcoin_core_money_range --run-ignored all \
  -E 'test(/axiomatic_span_byte_element_entries_verify|axiomatic_span_dynamic_extent_requirement|defaulted_span_arguments_import/)'
```

Bisected locally: all three pass on `ce7d52ff4` and fail from `52553ca05`
("Verify rbtree size callbacks and unify checked-step output bindings"),
which changed call requirement checking among much else.

Acceptance:

- A call requirement `A implies B` whose `A` the call's arguments decide false
  is discharged, as is one whose `B` follows from the facts.
- The three span tests pass, and a call with a concrete count past the view's
  end is still refused (`axiomatic_span_dynamic_extent_requirement_is_proved_before_view_recovery`
  covers the proved-before-recovery order).
