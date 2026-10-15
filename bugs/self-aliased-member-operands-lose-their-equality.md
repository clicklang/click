# Self-aliased member operands lose their equality

Soundness: incomplete. A defined C++ operation is refused as signed overflow,
and nothing false is accepted.

`FeeFrac::operator+=` and `operator-=` from the pinned Bitcoin Core fixture
read `this->size` and `other.size`. Under the contract `this == &other` both
reads name the same cell. `x - x` is 0, so `operator-=` is defined without
bounds, and `operator+=` is defined under the stated `size` bounds. Both
nightly tests now refuse the operation:

```text
FeeFrac::operator-=: `FeeFrac_operator_subtract_assign.contract` tactic 0:
`execute()` produced undefined behavior: signed overflow
  operation: `this->size - other.size`
  pure facts: [this == &other, viewable(((uint8 *)&this->size)[0..8]), ...]
```

```text
FeeFrac::operator+=: ... signed overflow
  operation: `this->size + other.size`
  pure facts: [-1073741824 <= old(this->size), old(this->size) <= 1073741823,
               ..., this == &other, ...]
```

Reproduce from a checkout with the pinned clang and exporter
(`docs/internals/testing.md`):

```sh
CLICK_NIGHTLY=1 RUST_MIN_STACK=8388608 \
CLICK_CPP_EXPORTER="$(scripts/build-cpp-exporter.sh)" \
cargo nextest run --test bitcoin_core_money_range --run-ignored all \
  -E 'test(/fee_frac_addself|fee_frac_subtractself/)'
```

Bisected locally: both pass on `842be5ca4` and fail from `b08e9207c` ("Remove
the general decision from simple checking"). Kernel condition evaluation now
asks only exact facts, the condition's own form and the difference graph. The
equality of the two loads through `this == &other` is no longer derived. The
cpp_import nightly tests
`subtraction_method_self_aliasing_is_defined_without_bounds_and_frames_caller_memory`
and `ordinary_value_methods_import_with_const_receiver_and_mixed_width_fields`
(case `double_size`) fail with the same refusal on master `26caef84b`.

Acceptance:

- With `this == &other`, `this->size - other.size` is defined with no bounds,
  and `this->size + other.size` is defined under the contract's bounds.
- `pinned_upstream_fee_frac_addself_reexports_and_verifies`,
  `pinned_upstream_fee_frac_subtractself_reexports_and_verifies` and the two
  cpp_import tests pass, within simple checking's complexity
  contract (`docs/internals/verification-efficiency.md`).
