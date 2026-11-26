# Differently written equivalent invariants retain their exit correspondence

`0 == 0` and `1 == 1` lower to the same semantic fact. Each declaration
retains its own correspondence, so the quantified invariant still names its
own checked fact at loop exit. The C is the original array-fill reproduction.

```c filename=probe_fill.c
int32 probe_fill(int32 p[], int32 lo, int32 hi, int32 v) {
    int32 i;
    i = lo;
    while (i < hi) {
        p[i] = v;
        i = i + 1;
    }
    return i;
}
```

```click
import click::separation;

verifying "probe_fill.c";

int32 probe_fill(int32 p[], int32 lo, int32 hi, int32 v) {
    requires 0 <= lo and lo <= hi and hi <= 1000;
    owns p[lo..hi];
    ensures result == hi;
    ensures forall (k: int32) { lo <= k and k < hi implies p[k] == v };
} by {
    step();
    step();
    loop fill {
        decreases to_integer(hi) - to_integer(i);
        invariant lo <= i;
        invariant i <= hi;
        invariant 0 == 0;
        invariant 1 == 1;
        invariant forall (k: int32) { lo <= k and k < i implies p[k] == v };

        initialize by {
            have lo <= i by close();
            have i <= hi by close();
            have 0 == 0 by close();
            have 1 == 1 by close();
            have forall (k: int32) { lo <= k and k < i implies p[k] == v } by {
                intro() {
                    intro() {
                        contradiction(lo <= k and k < i);
                    }
                }
            }
        }
        maintain by {
            mark iteration;
            step();
            step();
            have to_integer(at(iteration, i) + 1) == to_integer(at(iteration, i)) + 1;
            have 0 <= to_integer(hi) - to_integer(at(iteration, i) + 1);
            have forall (k: int32) { lo <= k and k < i implies p[k] == v } by {
                intro() {
                    intro() {
                        have lo <= k;
                        have k < i;
                        if k < at(iteration, i) {
                            have at(iteration, p[k]) == v by {
                                have at(iteration, lo) <= at(iteration, k) and at(iteration, k) < at(iteration, i);
                                instantiate(forall (cell: int32) {
                                    at(iteration, lo) <= at(iteration, cell) and at(iteration, cell) < at(iteration, i) implies
                                        at(iteration, p[cell]) == at(iteration, v)
                                }, k);
                                close();
                            }
                            have at(iteration, i) != k by { close() using { k < at(iteration, i); }; }
                            have at(iteration, separate(memory(p[i]), memory(p[k]))) by {
                                apply(separation::separate_elements(p, at(iteration, i), k));
                            }
                            have separate(loop(0).statement(0).footprint, memory(p[k])) by {
                                close() using { at(iteration, separate(memory(p[i]), memory(p[k]))); };
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
                            have k == at(iteration, i) by { close(); }
                            rewrite(k, at(iteration, i));
                            close();
                        }
                    }
                }
            }
            close();
        }
    }
    step();
    close();
}
```

```expect
pass
```
