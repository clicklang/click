# solve refutes a conjunct of an antecedent

`pick` returns `2` when `x > 100`. On that path the third postcondition's
antecedent `x != 0 and x <= 100` is false, because its conjunct `x <= 100`
contradicts the path's `x > 100`. `solve` introduces the antecedent, splits
it into its conjuncts, and closes the goal from the conjunct whose opposite
the facts hold, as it does for the curried `x != 0 implies x <= 100
implies ...`; the path states the opposite as `x > 100`, not as `x <= 100`
false, and either spelling is found.

```c filename=solve_refutes_a_conjunct_of_an_antecedent.c
uint32 pick(uint32 x) {
    if (x == 0) {
        return 1;
    } else if (x > 100) {
        return 2;
    } else {
        return 3;
    }
}
```

```click
verifying "solve_refutes_a_conjunct_of_an_antecedent.c";

uint32 pick(uint32 x) {
    ensures x == 0u32 implies result == 1u32;
    ensures x > 100u32 implies result == 2u32;
    ensures x != 0u32 and x <= 100u32 implies result == 3u32;
    ensures x != 0u32 implies x <= 100u32 implies result == 3u32;
}
```

```expect
pass
```
