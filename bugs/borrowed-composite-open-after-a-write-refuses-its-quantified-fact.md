# Opening a borrowed composite after a C write refuses its quantified fact

Soundness: incomplete. The kernel refuses an `open` whose body fact it can
reproduce itself; the refusal is a missing acceptance, and no false
acceptance is known.

A function that borrows a composite stating a quantified fact about its
viewed cells can open it at entry, but not after executing a C statement that
writes memory the composite does not view. The kernel rejects the checked
resource step with "resource rewrite produced an unchecked pure-fact delta".
The write cannot change the viewed cells: they are borrowed, and the written
cell is owned separately.

The likely cause, not yet confirmed: the Surface lowers the opened body fact
itself, with its own quantifier binder and a load variable named at the
current memory snapshot, while the kernel's delta check compares the
introduced fact exactly against its own instantiation of the definition,
which differs only by the binder (and so by the registered load the binder
appears in). At entry the open introduces nothing new, because the same
Surface spelling was already published and accepted through the kernel's
alpha-equal contract-entry check; after a write the snapshot differs, so the
fact is new and the exact comparison refuses it.

The diagnostic does not name the fact it could not reproduce, and
`--trace-proof` places the failure on the preceding `step()` with no checked
step for the `open`.

## Reproduction

Found while fixing `borrowed-byte-composite-open-rejects-quantified-fact`
(whose acceptance asked for the refusal to name the fact): that bug's entry
case now opens, and this variant still fails.

```c filename=probe.c
int first(int p[], int n, int q[])
{
	q[0] = 1;
	return p[0];
}
```

```click
resource nonzero(p: int32*, n: int32) {
    views p[0..n];
    fact forall (k: int32) { 0 <= k and k < n implies p[k] != 0 };
}

verifying "probe.c";

int32 first(int32 p[], int32 n, int32 q[]) {
    requires 0 < n;
    views nonzero(p, n);
    owns q[0..1];
    ensures result != 0;
} by {
    step();
    open(nonzero(p, n)) {
        execute();
        simp();
    }
}
```

Observed on branch `cstrbugs` (master `afbe407a` plus the fixes for the
three `cstr_at` bugs): `kernel rejected checked resource open: resource
rewrite produced an unchecked pure-fact delta`, reported at the `step()`.
Without the leading `step()` the proof verifies.

## Acceptance

- The reproduction verifies as written, kept as an mdtest.
- The Surface and the kernel produce the same proposition for the opened
  fact, or the kernel's delta check relates them by a checked alpha
  equivalence that includes registered loads; it is not otherwise weakened.
- When the delta check refuses, the diagnostic or trace names the fact it
  could not reproduce, at the `open` that introduced it.
