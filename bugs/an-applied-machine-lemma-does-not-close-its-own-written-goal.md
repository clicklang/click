# An applied machine lemma does not close its own written goal

Soundness: incomplete. A provable goal is refused; nothing false verifies.

## Violated invariant

A comparison of exact observations is the native comparison it observes
(`docs/reference/language/index.md`, Integer specification arithmetic), so a
fact and a goal written with the same source proposition are one fact.
`assumption` is a simple tactic: a refusal within its documented behavior is a
bug. With a `uint32` difference against the type's maximum on one side, the
goal is lowered to its Integer reading (`to_integer(left) <= 4294967295 -
to_integer(right)`) while the conclusion of
`click::integer::uint32_add_guard_by_integer_bound`, applied with the same
arguments, is recorded in its native form (`left <= 4294967295u32 - right`).
Neither closing the script nor `assumption` connects the two.

## Reproduction

```click
import click::integer;

theorem use_guard(left: uint32, right: uint32) {
    requires to_integer(left) + to_integer(right) <= 4294967295;
    ensures left <= 4294967295u32 - right by {
        apply(uint32_add_guard_by_integer_bound(left, right));
        assumption();
    }
}
```

`assumption` refuses: "`assumption` requires the current goal as an available
semantic fact; current goal is an Integer less-or-equal fact", with goal
`to_integer(left) <= 4294967295 - to_integer(right)`. Without the
`assumption()` step the script ends "with its goal still open". The same
claim restated from a native premise (`requires left <= 4294967295u32 -
right; ensures left <= 4294967295u32 - right;`) verifies.

The nightly fixture `mdtests/stdlib_every_symbol.md` fails on this at
`use_uint32_add_guard_by_integer_bound`, which states the guard's own
conclusion and proves it by the guard alone.

The same refusal occurs for a signed operand whose definedness follows from
the premise, so the defect is not specific to unsigned subtraction:

```click
import click::machine_integer;

theorem successor_bound(value: int32, upper: int32) {
    requires value < upper;
    ensures value + 1 <= upper by {
        apply(int32_increment_upper_bound(value, upper));
        assumption();
    }
}
```

The goal is `to_integer(value) + 1 <= to_integer(upper)`; the applied
conclusion is the native `value + 1 <= upper`. The scaling fixture
`a_fixed_store_proof_costs_the_same_after_a_growing_unrelated_proof`
(nightly) fails on the converse: a later `apply(int32_increment_upper_bound(s
+ i, l)) using { s + i < l; }` cannot find its native premise after
`s + i < l` was proved and recorded in its Integer reading.

A related symptom: in the adler2 `U32X4::add_assign` proof
(`design/adler32/project/adler2/helpers.click`), replacing each
`apply(uint32_add_guard_by_integer_bound(self.0[i], other.0[i]))` with
`have self.0[i] <= 4294967295u32 - other.0[i] by auto();` proves each `have`,
but `execute()` then cannot discharge Rust's add panic check
`(old(*self) as u32) <= (-1 - old(*<pointer A>) as u32)` from it: the
Integer-read fact is not the native prerequisite. The guard theorem's native
conclusion is still required there.

## Acceptance

- The reproduction verifies, with and without the `assumption()` step.
- `mdtests/stdlib_every_symbol.md` verifies under `MDTEST_FILTER`.
- A `have` of `left <= 4294967295u32 - right` proved from the Integer bound
  discharges the Rust narrow addition check, or the reference documents why
  the native guard theorem is the required route.
