# A `uint64` induction hypothesis captures the measure when the goal omits it

Soundness: not soundness. The hypothesis Click adds is weaker than the
documented one, not stronger: its decrease guard reads `n < n`, which never
holds, so the hypothesis is vacuously true and cannot be used. Nothing false
can follow from it; a valid proof is refused.

The violated invariant: after `induct(n) as ih` on a `uint64` parameter, `ih`
is "for every `m`, `m < n` and the requirements at `m` imply the goal at `m`"
([scalar induction](../docs/reference/tactics/index.md#scalar-induction)),
with the bound variable distinct from the outer `n`. When neither the goal nor
any requirement mentions `n`, the `uint64` hypothesis instead names its bound
variable `n` itself, so the guard `m < n` becomes `n < n` under the binder.
The trace shows the captured form:

```text
tactic@7: induct
  adds: ∀n:CMachineInteger(UInt64). (uint64 <(n, n) is true ⇒ bits64 =(k(uint64(3u64)), 3u64) is true)
```

The same shape over `int32` (with `requires n >= 0;`) verifies, and a
`uint64` theorem whose goal mentions `n` verifies.

```c filename=z.c
void unused() {}
```

```click
verifying "z.c";

function k(x: uint64) -> uint64 { x }

theorem t(n: uint64) {
    ensures k(3u64) == 3u64 by {
        induct(n) as ih;
        if n <= 0u64 {
            unfold(k(3u64));
            normalize();
        } else {
            have 0u64 < n by simp();
            have n - 1u64 < n by arithmetic() using { 0u64 < n; };
            apply(ih(n - 1u64)) using { n - 1u64 < n; };
        }
    }
}
```

`click verify` prints:

```text
proof error:
  `apply` of the induction hypothesis failed
  instantiated premise `n - 1u64 < n - 1u64` does not follow from the listed evidence

tactic@14:
  apply(ih(n - 1u64)) using { n - 1u64 < n; };
goal: k(3u64) == 3u64
refused by: `apply` (simple: a refusal within its documented behavior is a bug)
see: click docs apply
```

The bare form misreports the guard. Replacing the last two `else` steps with
`apply(ih(n - 1u64));` prints:

```text
proof error:
  induction hypothesis `ih` could not prove premise `(n - 1u64) < n`
```

although `n - 1u64 < n` follows from the `0u64 < n` fact on hand; the
premise actually checked is `n - 1u64 < n - 1u64`.

A goal that never mentions the measure is degenerate, but it does occur when a
theorem keeps a parameter for its callers' sake, and the documented hypothesis
is well defined for it.

## Acceptance criteria

- The reproduction verifies, and its trace shows the hypothesis with a bound
  variable distinct from `n`, guarded by `m < n` (whatever the fresh name).
- The bare `apply(ih(n - 1u64))` variant also verifies.
- When an instantiated guard is refused, the bare form prints the guard
  actually checked, the same text as the `using` form.
- A regression keeps this source pattern: a `uint64` `induct` whose goal and
  requirements do not mention the measure.
