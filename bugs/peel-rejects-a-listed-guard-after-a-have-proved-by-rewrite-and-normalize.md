# Peel rejects a listed guard after a have proved by rewrite and normalize

Soundness: incomplete. A valid proof is refused, and `click expand` writes
an expansion that does not re-verify; nothing false is accepted.

`peel(f(...)) using { G; }` accepts its guard `G` when the `have G;` before
it was proved by the implicit `solve`, and refuses the same guard when that
`have` was proved by `rewrite(...); normalize();`. The recorded fact is the
same term in both, and `peel` lowers the listed premise and the defining
equation to the same terms in both. So the decision depends on state the
earlier `solve` left behind, not on `peel`'s inputs.

Because expansion replaces the `solve` with the explicit tactics, the
expanded proof fails where the original passed: two proof tools disagree.

Invariant: a simple tactic's result is a function of the goal, the listed
premises and the facts (`docs/internals/verifier-design.md`); `click expand`
output re-verifies.

## Reproduction

`design/charon-trial/slice-iter/sum.click` verifies. Replace its entry block

```click
    have prefix(bytes, bytes.len() - loop(0).iter.len()) == 0 by {
        have to_integer(bytes.len() - loop(0).iter.len()) <= to_integer(0u64);
        peel(prefix(bytes, bytes.len() - loop(0).iter.len())) using {
            to_integer(bytes.len() - loop(0).iter.len()) <= to_integer(0u64);
        }; solve();
    }
```

with the form expansion writes for the inner `have`:

```click
    have prefix(bytes, bytes.len() - slice_iter::len(iter)) == 0 by {
        have to_integer((bytes.len() - slice_iter::len(iter))) <= to_integer(0u64) by {
            rewrite(at(function.entry, slice_iter::len(__rust_mir_4)) == at(function.entry, __rust_checked_3));
            normalize();
        }
        peel(prefix(bytes, bytes.len() - slice_iter::len(iter))) using {
            to_integer(bytes.len() - slice_iter::len(iter)) <= to_integer(0u64);
        }; solve();
    }
```

```text
`peel(prefix(...)) using` found no listed guard that decides the range. The
empty-range equation needs `to_integer(bytes.len() -
click::rust::slice_iter::len::<uint8>(<unnamed A>)) <= 0`; ...
```

Keeping the second block but deleting the `by { rewrite(...); normalize(); }`
body, so the inner `have` is proved by `solve`, verifies again.

Observed with probes: in both variants the inner `have` adds
`uint64 <=(uint64((bytes_len - slice_iter::len(iter))), 0u64)`, and
`function_range_fold_step`'s lowered premise and `equality`
(`src/surface/proof/proof_object/resource_steps.rs`) print identically. The
required guard is the Integer condition `to_integer(x) <= 0`; the listed one
is a native `uint64` comparison. What bridges them after `solve`, in
`discharge_restated_fold_law` / `exact_fact_is_available`, was not found.

The direct symptom: `click expand --claim sum.contract` on the fixture fails
with "expanded proof did not verify", and `click audit` reports one claim
failure. The old hidden-state example
(`examples/rust-iter-references/sum.click`) is unaffected: there the inner
`have` expands to `normalize()` alone.

Two smaller observations from the same expansion, not investigated:

- the rewrite equality is spelled
  `at(function.entry, slice_iter::len(__rust_mir_4)) == at(function.entry, __rust_checked_3)`,
  compiler temporaries read at function entry, for a fact a call's contract
  gave;
- outside the loop the expansion spells `loop(0).iter` as the program's own
  local `iter`.

## Acceptance criteria

- The second block above verifies.
- `click expand --claim sum.contract` on
  `design/charon-trial/slice-iter/sum.click` re-verifies, with a nightly
  tools test beside `charon_slice_iter_sums_bytes_by_its_library_contract`.
- A regression shows `peel` deciding its guard identically whether the
  guard's `have` was proved by `solve` or by explicit simple tactics.
