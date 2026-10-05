# A pure witness cannot evaluate a declaration-level let alias

## Violated invariant

An immutable declaration-level alias that is in scope for a theorem's goal
must also be usable as its witness value. The goal lowers `saved` correctly,
but witness evaluation sees no binding for it:

```click
theorem retain(p: int32*) {
    let saved = p;
    ensures exists (q: int32*) { q == saved } by {
        witness { q: saved };
        simp();
    }
}
```

After the pure C witness dispatch fix, this fails with an `unbound variable` error naming `saved`. Witness capture uses theorem parameter values and proof locals;
the declaration alias has already disappeared from the theorem definition
without being substituted into the written witness.

## Intended regression and acceptance criteria

- The theorem above verifies, as does its int32 counterpart.
- Alias capture retains the outer binding when an existential or a nested
  quantifier shadows the parameter or alias name.
- A false body still fails; expansion retains the same binding and re-verifies.
- Run the focused alias and witness tests and `scripts/check.sh`.
