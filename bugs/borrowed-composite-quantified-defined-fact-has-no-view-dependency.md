# A borrowed composite's quantified `defined` fact has no view dependency

Soundness: incomplete. The check refuses a fold or open whose quantified
`defined(p[k])` fact reads only cells inside the composite's own viewed range;
it never accepts a read outside that range.

A composite whose body views `p[0..n]` and states
`forall (k) { 0 <= k and k < n implies defined(p[k]) }` cannot be opened by a
function that borrows it, and cannot be folded from a borrowed view even at a
`produces` return. The dynamic dependency check rejects the fact: "current
body fact reads memory outside every live viewed-memory dependency". The same
body with a quantified value fact instead, such as `p[k] == 0` over `int32`
cells, opens and folds. The check appears to look up a view for the cell
`p[k]` without the quantifier's guard `k < n`, so no view covers it.

The declaration itself is accepted: the resource coverage check does use the
guard.

## Reproduction

Found while prototyping a borrowed C-string resource (`cstr_at` in
`library/cstr.click` on branch `cstrview`), whose body states that every byte
through the terminator is defined, as `cstr_readable_len` does.

```c filename=probe.c
int32 first(int32 p[], int32 n) { return p[0]; }
```

```click
resource valid(p: int32*, n: int32) {
    views p[0..n];
    fact forall (k: int32) { 0 <= k and k < n implies defined(p[k]) };
}

verifying "probe.c";

int32 first(int32 p[], int32 n) {
    requires 0 < n;
    views valid(p, n);
    ensures true;
} by {
    open(valid(p, n)) {
        execute();
    }
}
```

Observed on master `5ad27faf`: `unfold(valid(p, n)) rejected dynamic body
dependency`. The diagnostic also names `unfold` for the `open` the proof wrote.

The fold side fails the same way: a function with `views p[0..n]` and the
matching requirement cannot `produces valid(p, n)` with `execute(); fold(valid(p, n));`.

## Acceptance

- The reproduction verifies as written, kept as an mdtest, together with a
  `produces` fold of the same resource from a borrowed view.
- A quantified `defined` read whose guard does not place the cell inside a
  live viewed range is still refused.
- The dependency lookup stays local to the fact's reads; no scan of unrelated
  views is added.
