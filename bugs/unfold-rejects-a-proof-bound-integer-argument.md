# `unfold` rejects a call whose argument names a proof-bound `Integer`

Soundness: incomplete. `unfold` refuses a true defining equation; nothing is
accepted that should not be.

`unfold(f(args))` exposes the defining equation of a pure-function call. It
works when an `Integer` in `args` is a theorem parameter, but fails when the
`Integer` was bound inside the proof by `obtain` or `intro`, although both
bind it as a proof-local `Integer` that other steps (`have`, `rewrite`,
`auto`) accept.

Reproduced on master `6d62a0f3`:

```click
spec enum Walk { At(Integer, Walk), Done }

function black(w: Walk) -> int32 decreases w {
    match w { Walk::At(wd, rest) => black(rest), Walk::Done => 1 }
}

theorem unfold_an_introduced_integer(rest: Walk) {
    requires black(rest) == 1;
    ensures forall (d: Integer) { black(Walk::At(d, rest)) == 1 } by {
        intro();
        unfold(black(Walk::At(d, rest)));
        assumption();
    }
}
```

fails at the `unfold` with `could not lower defining equation for `black`:
expected a specification-side Integer expression`. Opening the same value
with `obtain (d: Integer) { ... }` and then
`unfold(black(Walk::At(d, rest)))` fails with `` `d` is not an Integer
binding``. With `d` a theorem parameter instead, the same `unfold` succeeds.

Acceptance: an mdtest proves `unfold_an_introduced_integer` as written, and a
second one unfolds the same call after `obtain`; both diagnostics are gone,
and an `unfold` naming an unbound `d` is still refused.
