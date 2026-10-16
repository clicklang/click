# Symbolic range refold refusal exceeds its deterministic work bound

Soundness: not soundness. The valid current-value claim verifies and the
invalid entry-value claim is rejected. The nightly regression fails because
rejecting the latter costs more than its existing deterministic work bound;
no false acceptance is known.

Reproduced on `a6bf8166f4a079874ff992393c44b6803102cbe8`, then rechecked
after merging master through `548dfd9408599db9c7a89b2e55b344c87902c895`
(including the shared arithmetic fixes), with:

```sh
cargo nextest run --profile nightly --lib --run-ignored only \
  -E 'test(symbolic_read_refold_and_refusal_do_not_enumerate_range_elements)'
```

The fixture preserves this C:

```c
int32 read_after_store(int32 *a, int32 k) {
    a[3] = 5;
    return a[k];
}
```

A Click resource owns `a[0..length]`, with `0 <= k < length`. Its proof
unfolds the resource, executes the unchanged C, refolds, and runs `simp()`.
The postcondition `result == a[k]` verifies; `result == old(a[k])` must fail
because `k` can equal `3`.

For the rejected claim, the existing scaling regression measures total work
`[59841, 59820, 60188]` at lengths `[64, 4096, 1048576]`, exceeding its
unchanged 30,000-unit bound. After the master update the totals are
`[62744, 63047, 63847]`: the last increase of 800 also exceeds the test's
512-unit allowance for eight additional length bits. Fold work remains
exactly 150 units at each length in both runs, so this reproduction does
not show per-element fold enumeration.
Profiling the original small rejected sidecar attributes most work to failed
`simp closure: snapshot transport` attempts. Treat that as a lead, rather
than evidence that every transport attempt is redundant.

Acceptance criteria:

- Restore the named regression under its existing work bounds, including
  its bit-length growth allowance and constant fold cost. Do not raise them.
- Keep both the valid-current-value proof and the old-value rejection,
  including the diagnostic identifying the potentially aliasing store.
- Preserve existing snapshot-transport expansion and independent rechecking
  controls. A search optimization must still emit ordinary checked steps.
