# A `have` over a rewritten machine sum refuses to lower its definedness

The nightly mdtest `mdtests/return_fold_retains_transported_facts.md` fails
on `master` (`61dbea03a`), and already failed before `497dbdcdd`. It is in
`NIGHTLY`, so the gate does not run it.

## Reproduction

```sh
MDTEST_FILTER=return_fold_retains_transported RUST_MIN_STACK=8388608 \
  cargo test -q --test mdtests mdtests
```

```text
`arena_write.contract` proof step tactic 7: could not lower `have` proposition:
the proposition `to_integer((region->start + index + 1)) <= to_integer(old(r.end))`:
its subterm `*(region + 2) + index + 1` denotes a value only where 1 condition of
that evaluation holds, and the premises in scope where it is stated establish 0
of them, not this one.
  not established: `*(region + 2) + index + 1` must not overflow
```

Tactic 7 is
`have to_integer(region->start + index + 1) <= to_integer(e) by { rewrite(region->start == s); assumption(); }`.
The facts before it include `region->start == s`,
`to_integer(s + index + 1) <= to_integer(e)` (proved by
`integer::int32_increment_upper_bound`) and `to_integer(s + index) < to_integer(e)`, so
`s + index + 1` cannot overflow, and nor can the same sum with
`region->start` in place of `s`. The mdtest was last edited by `c831474f6`
("Delete width-specific bridge lemmas Integer-default arithmetic replaces").

## Violated invariant

A stated proposition whose machine subterm is defined under the premises in
scope lowers. Here the definedness of `region->start + index + 1` follows from
an equality to `s` and from the bound proved for `s + index + 1`, which are
both in scope.

## Acceptance criteria

- The mdtest passes again in the nightly suite, with its proof unchanged or
  with a migration that keeps its C and states why the old script no longer
  applies.
- If the cause is a lowering change that the gate can see, a small gate mdtest
  covers a `have` over a sum whose definedness follows from an equality to a
  name whose bound is in scope.
