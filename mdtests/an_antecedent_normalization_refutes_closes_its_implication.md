# A false antecedent closes its implication

Specification arithmetic compares exact Integers. The assumption
`to_integer(i) + 1 == to_integer(i)` is contradictory because adding one
changes the value.

The first proof introduces the assumption and applies `contradiction`.
The other claims exercise the explicit and implicit closers on the same
false assumption. A loop-entry invariant such as
`i == at(loop(0).entry, i) + 1 implies n <= 5u64` has the same form when
`i` is still its entry value.

```c filename=refuted_antecedent.c
int r(int i, unsigned long n) { return i; }
```

```click
verifying "refuted_antecedent.c";

int32 r(int32 i, uint64 n) {
    requires 0 <= i and i < 4;
    ensures true;
} by {
    have to_integer(i) + 1 == to_integer(i) implies n <= 5u64 by {
        intro() {
            contradiction(to_integer(i) + 1 == to_integer(i));
        }
    }
    have i == i + 1 implies n <= 5u64 by { close(); }
    have i <= i + 4 implies i == i + 1 implies n <= 5u64;
}
```

```expect
pass
```
