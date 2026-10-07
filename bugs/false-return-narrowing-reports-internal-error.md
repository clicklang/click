# A decidably false return narrowing reports an internal error, not the range

## Violated invariant

Returning an `int32` from a `uint8` function owes the range `0 <= x <= 255`
(`docs/internals/kernel.md`, narrow conversions). When the facts decide the
range false the proof should be refused with a diagnostic naming the
conversion and the value, as a narrowing store or a call argument is. Instead
the proof object reports an internal inconsistency:

```text
`f.contract`
the proof object could not complete its checked function execution
a published path outcome is not its trace's outcome
```

The verdict is right and the message is wrong: it names no construct, no
value, and no bound, and reads as a kernel defect. The return conversion in
`src/kernel/eval/expression.rs` (`coerce_c_value_to_type` through
`evaluate_c_cast_paths`) files the range as an obligation the facts then
refute, and the published outcome of the path disagrees with the recorded
trace's outcome at `trace_completion` in `src/kernel/proof/execution.rs`.
Related wrong spellings in the same family, each with a correct verdict: a
decidably false narrowing initializer (`uint8 y = x` with `x == 300`) and an
out-of-range constant float-to-integer cast are reported as `type mismatch`.

## Reproduction

```c filename=narrow.c
uint8 f(int32 x) { return x; }
```

```click
verifying "narrow.c";
uint8 f(int32 x) {
    requires x == 300;
    ensures result == 44;
} by { execute(); simp(); }
```

Observed on 2026-10-07: exit 1 with the internal message above, for both
`execute(); simp();` and `auto`.

## Intended regression

The reproduction as a negative mdtest whose `expect` names the `uint8` range
and the value `300`, and a sibling with `requires x == 44` that verifies.

## Acceptance criteria

- A return conversion whose range the facts refute is refused with a
  diagnostic naming the target type's range and the returned value.
- The message `a published path outcome is not its trace's outcome` is not
  reachable from a false narrowing.
- `scripts/check.sh` passes.
