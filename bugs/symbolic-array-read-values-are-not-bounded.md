# A symbolic read of an initialized array has no usable value

## Violated invariant

After PR #53, `values[x]` over a fully initialized local array, under
`0 <= x && x < 4`, is accepted as an initialized read, but its value is
unknown. A claim that follows from the contents does not verify:

```c
int32 f(int32 x) {
    int32 values[4] = {1, 2, 3, 4};
    int32 r = 0;
    if (0 <= x && x < 4) { r = values[x]; }
    return r;
}
```

`ensures result >= 0 && result <= 4` fails. Two causes were observed: the load
splits once per stored cell and leaves a final case (`0 <= x < 4` with
`x != 0, 1, 2, 3`) that nothing refutes; and an all-equal array (`= {0}`) is
not reduced to its run's constant. The refusal in that case also blames a store
to `values+12`, which misattributes the cause.

## Intended regression

Mdtests: the program above with that `ensures`; `= {0}` with `ensures result
== 0`; a heap and a global variant. Negatives: `ensures result >= 2` for
`{1,2,3,4}` is refused.

## Acceptance criteria

- A symbolic read whose index is bounded to the array has a value the standard
  check can bound: either the impossible residual case is refuted from the
  index bounds and the cell offsets, or a run read returns the run's value.
- The positives verify, the negatives are refused, and the misattributed store
  no longer appears in the refusal.
