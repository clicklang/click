# The back edge splits a universal at an incremented index

After `p[j] = 0; j = j + 1;`, the invariant
`forall (k: int32) { 0 <= k and k < j implies p[k] == 0 }` at the back edge
covers one more cell than at iteration entry. The proof saves the entry index
and splits at that index. Below it, the entry invariant supplies the value and
the store preserves the cell. At the index itself, the store supplies the new
value. An integer observation of the increment also establishes that the
remaining distance to 3 decreases.

```c filename=zero3.c
int32 zero3(int32 p[3]) {
    int32 j;
    j = 0;
    while (j < 3) {
        p[j] = 0;
        j = j + 1;
    }
    return 0;
}
```

```click
import click::separation;

verifying "zero3.c";

int32 zero3(int32 p[3]) {
    consumes p[0..3];
    ensures result == 0;
} by {
    step();
    step();
    loop {
        decreases to_integer(3) - to_integer(j);
        invariant j >= 0 and j <= 3;
        invariant forall (k: int32) { 0 <= k and k < j implies p[k] == 0 };
        maintain by {
            mark iteration;
            step();
            step();
            have to_integer(at(iteration, j) + 1) == to_integer(at(iteration, j)) + 1;
            have 0 <= to_integer(3) - to_integer(at(iteration, j) + 1);
            have forall (k: int32) { 0 <= k and k < j implies p[k] == 0 } by {
                intro() {
                    intro() {
                        have 0 <= k;
                        have k < j;
                        if k < at(iteration, j) {
                            have at(iteration, p[k]) == 0 by {
                                have at(iteration, 0) <= at(iteration, k) and at(iteration, k) < at(iteration, j);
                                instantiate(forall (cell: int32) {
                                    at(iteration, 0) <= at(iteration, cell) and at(iteration, cell) < at(iteration, j) implies
                                        at(iteration, p[cell]) == at(iteration, 0)
                                }, k);
                                close();
                            }
                            have at(iteration, j) != k by { close() using { k < at(iteration, j); }; }
                            have at(iteration, separate(memory(p[j]), memory(p[k]))) by {
                                apply(separation::separate_elements(p, at(iteration, j), k));
                            }
                            have separate(loop(0).statement(0).footprint, memory(p[k])) by {
                                close() using { at(iteration, separate(memory(p[j]), memory(p[k]))); };
                            }
                            have at(loop(0).statement(0).exit, p[k]) == at(iteration, p[k]) by {
                                preserve(memory(p[k]), loop(0).statement(0));
                            }
                            have separate(loop(0).statement(1).footprint, memory(p[k])) by { close() using {}; }
                            have p[k] == at(loop(0).statement(1).entry, p[k]) by {
                                preserve(memory(p[k]), loop(0).statement(1));
                            }
                            close();
                        } else {
                            have k == at(iteration, j) by { close(); }
                            rewrite(k, at(iteration, j));
                            close();
                        }
                    }
                }
            }
            close();
        }
        owns p[0..3];
    }
    step();
}
```

```expect
pass
```
