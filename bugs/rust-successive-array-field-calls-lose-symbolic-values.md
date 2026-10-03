# Successive calls on local Rust array fields lose symbolic values

The caller must retain a callee's checked value postconditions with their proper
entry and exit memory snapshots. Two ordinary calls on a locally constructed
array-field record currently fail to establish their symbolic composition.

Use `design/charon-trial/assignment-operators/operators.click` and its locked
source/artifact. In a temporary copy, change only the `local` contract's
`requires a == 6u32; requires b == 2u32;` to
`requires a <= 1000u32; requires b <= 1000u32;`. Keep all imported source bodies
and other contracts unchanged. Run `click verify` on that copy with the existing
import config/lock. The true postcondition is
`result == ((a * 2u32 % 7u32) ^ (b * 2u32 % 7u32))`.

Observed: `execute()` completes, but `simp()` cannot close `local.ensures_0`.
Its rendered facts include `load(&words) == (a * 2)` and
`load(&words) == (load(&words) % 7)`, while the resulting lane cannot be related
to `(a * 2) % 7`. Each method and direct wrapper verifies separately; the
concrete two-call case also verifies. The problem remains after importing the
methods as ordinary calls, without any operator-specific execution.

Investigate snapshot identity, postcondition instantiation and transport rather
than changing the frozen Rust body. Diagnostic loads omit snapshot identity, so
these renderings alone do not establish a soundness defect.

Acceptance: the symbolic local composition verifies and its expanded proof
rechecks; unchanged-lane and omitted-remainder false claims fail. Include a
small ordinary-call regression and ensure snapshot bookkeeping remains bounded
by touched fields rather than array extent.
