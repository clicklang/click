# Restricted `simp` after execution misses a conjunct the return value decides

## Violated invariant

`simp() using { ... }` after execution restricts the premises `simp` may
cite. The checked outcome itself (that `result` is the returned value) is not
a premise, so a restricted `simp` should still close a claim whose remaining
conjuncts are the listed premises. `docs/concepts/proof-scripts.md` and
`mdtests/proof_script_execute_and_simp_using.md` show exactly this script.

Today the restricted `simp` refuses the claim. The mdtest passed only because
a written closer that closed nothing was skipped and the implicit `auto`
closed the claim.

## Reproduction

`checked_index.c`:

```c
int32 checked_index(int32 i, int32 n) {
    return i;
}
```

`s.click`:

```
verifying "checked_index.c";
int32 checked_index(int32 i, int32 n) {
    requires i >= 0;
    requires i < n;
    ensures in_range: 0 <= i and i < n and result == i by {
        execute();
        simp() using { 0 <= i; i < n; };
    }
}
```

`click verify s.click` verifies, but `click expand s.click:7` prints the
proof without the `simp() using`: the restricted `simp` closes nothing and
is skipped (`bugs/written-simp-that-closes-nothing-is-skipped.md`), and the
implicit `auto` closes the claim. With that skip removed, the restricted
`simp` is refused with "unclosed goal 0 <= i and i < n and result == i" and
the pure facts `[i >= 0, i < n]`. Listing the premises as `i >= 0; i < n;`
behaves the same way.

## Intended regression

`mdtests/proof_script_execute_and_simp_using.md` passes with the written
`simp() using` closing the claim, and its `click expand` output verifies.

## Acceptance criteria

- A restricted `simp` after execution closes a claim whose conjuncts are the
  listed premises and facts the checked outcome decides.
- A restricted `simp` still refuses a goal that needs an unlisted premise.
