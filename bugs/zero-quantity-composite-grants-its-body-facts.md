# Owning zero of a composite grants its body facts

Soundness: unsound. A function that owns `amount of bundle(n)` assumes the
pure body facts of `bundle(n)` at entry even when `amount == 0`, when it holds
no instance of the body at all. A caller that passes `0` therefore receives a
postcondition built on a body fact that need not hold. Here `probe(0, 5)`
yields `5 == 3`, and the caller verifies `ensures 1 == 0`. Reproduced on
master after #1018, with a change that only removes simple-tactic searches and
so can only make fewer proofs verify.

Priority: P1.

A body fact describes each instance a quantity counts. With a quantity of zero
there is no instance, so no body fact is available. With a symbolic quantity,
a body fact is available only where the quantity is known to be positive.

## Reproduction

```c filename=sound.c
void probe(int32 amount, int32 n) {}
int32 caller() {
    probe(0, 5);
    return 0;
}
```

```click
abstract resource atom();
resource bundle(n: int32) {
    owns atom();
    fact n == 3;
}
verifying "sound.c";
void probe(int32 amount, int32 n) {
    requires amount == 0;
    owns amount of bundle(n);
    ensures n == 3;
} by {
    execute();
}
int32 caller() {
    ensures 1 == 0;
} by auto;
```

`click verify` reports `2 selected proofs verified`. Removing the call from
`caller`, or calling `probe(0, 3)`, makes `caller` fail as it should; the false
postcondition comes from `probe`'s contract.

## Acceptance criteria

- `probe` above is refused: with `amount == 0`, `n == 3` is not available.
- A body fact of `amount of R(..)` is available at entry only when `amount > 0`
  is decided there; `observe(amount of R(..))` already projects the body only
  then (`src/surface/proof/resources.rs`, the explicit-quantity branch).
- An mdtest keeps this reproduction as an expected failure, and a positive
  mdtest shows the body fact used under `requires amount > 0`.
