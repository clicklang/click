# Iterated ownership: a run scan crosses the end of its locals

`scan_run` counts the current run of free cells while a loop owns an
`arena_scan` window carrying the map, the iterated ownership of the free
cells, and the run's bounds as fields; one arm resets the run to `0`.

The then-arm reasons over snapshot-relative order facts
(`at(iteration, i) < at(iteration, i) + 1` beside `i == at(iteration, i) + 1`),
which the context consistency check must examine without declaring the
context contradictory. At the return the function's locals end, and the
snapshot after their lifetime ends has the same content as one recorded
before they were declared, so its history does not pass through the snapshot
the step started from. Invalidating iterated facts across that step must walk
both sides back to their common ancestor rather than the later side alone.

```c filename=iterated_ownership_run_scan_crosses_its_locals_ending.c
int32 scan_run(int32* data, int32* occupied, int32 capacity) {
    int32 i;
    int32 run_length;

    i = 0;
    run_length = 0;
    while (i < capacity) {
        if (occupied[i] == 0) {
            run_length = run_length + 1;
        } else {
            run_length = 0;
        }
        i = i + 1;
    }
    return run_length;
}
```

```click
resource arena_cells(data: int32*, occupied: int32*, capacity: int32) {
    owns occupied[0..capacity];
    forall (k: int32) where 0 <= k and k < capacity {
        if occupied[k] == 0 {
            owns data[k..k + 1];
        }
    }
}

resource arena_scan(data: int32*, occupied: int32*, capacity: int32) {
    field lo: int32;
    field hi: int32;
    owns occupied[0..capacity];
    forall (k: int32) where 0 <= k and k < capacity {
        if occupied[k] == 0 {
            owns data[k..k + 1];
        }
    }
    fact 0 <= lo;
    fact lo <= hi;
    fact hi <= capacity;
}

verifying "iterated_ownership_run_scan_crosses_its_locals_ending.c";

int32 scan_run(int32* data, int32* occupied, int32 capacity) {
    owns arena_cells(data, occupied, capacity);
    requires 0 <= capacity;
} by {
    unfold(arena_cells(data, occupied, capacity));
    step();
    step();
    step();
    step();
    let run = fold(arena_scan(data, occupied, capacity), {
        lo: 0, hi: 0
    });
    loop as find_first_free_run {
        decreases capacity - i;
        owns run: arena_scan(data, occupied, capacity);
        invariant run.hi == i;
        invariant run.lo + run_length == i;
        invariant 0 <= run_length and run_length <= i;

        initialize by simp;
        preserve by {
            mark iteration;
            let { lo: lo, hi: hi } = unfold(run);
            have hi == i by {
                simp();
            }
            have lo + run_length == i by {
                simp();
            }
            have lo <= i by {
                simp() using {
                    lo <= hi;
                    hi == i;
                }
            }
            have 0 <= i by {
                apply(int32_le_transitive(0, lo, i)) using {
                    0 <= lo;
                    lo <= i;
                }
            }
            have i + 1 <= capacity by {
                apply(int32_increment_upper_bound(i, capacity)) using {
                    i < capacity;
                }
            }
            if occupied[i] == 0 {
                have run_length < capacity by {
                    arithmetic() using {
                        run_length <= i;
                        i < capacity;
                    }
                }
                branch then {
                    step();
                } else {
                    contradiction(not (occupied[i] == 0));
                }
                step();
                have hi == at(iteration, i) by {
                    simp();
                }
                have i == at(iteration, i) + 1 by {
                    normalize();
                }
                have lo <= at(iteration, i) by {
                    simp() using {
                        lo <= hi;
                        hi == at(iteration, i);
                    }
                }
                have at(iteration, i) < at(iteration, i) + 1 by {
                    apply(int32_increment_strictly_increases(
                        at(iteration, i),
                        at(iteration, capacity)
                    )) using {
                        at(iteration, i) < at(iteration, capacity);
                    }
                }
                have at(iteration, i) < i by {
                    rewrite(i == at(iteration, i) + 1);
                    assumption();
                }
                have at(iteration, i) <= i by {
                    apply(int32_lt_implies_le(at(iteration, i), i)) using {
                        at(iteration, i) < i;
                    }
                }
                have lo <= i by {
                    apply(int32_le_transitive(lo, at(iteration, i), i)) using {
                        lo <= at(iteration, i);
                        at(iteration, i) <= i;
                    }
                }
                have i <= capacity by {
                    simp();
                }
                have run_length == at(iteration, run_length) + 1 by {
                    normalize();
                }
                have lo + at(iteration, run_length) == at(iteration, i) by {
                    simp();
                }
                have lo + run_length == i by {
                    rewrite(run_length == at(iteration, run_length) + 1);
                    rewrite(i == at(iteration, i) + 1);
                    simp();
                }
                have 0 <= run_length and run_length <= i by {
                    simp();
                }
                let run = fold(arena_scan(data, occupied, capacity), {
                    lo: lo, hi: i
                });
                have run.hi == i by {
                    simp();
                }
                have run.lo + run_length == i by {
                    simp();
                }
                have 0 <= at(iteration, i) by {
                    assumption();
                }
                have 0 <= capacity - at(iteration, i) - 1 by {
                    arithmetic() using {
                        0 <= at(iteration, i);
                        at(iteration, i) < at(iteration, capacity);
                        0 <= capacity;
                    }
                }
                have capacity - at(iteration, i) - 1
                    < capacity - at(iteration, i) by {
                    arithmetic() using {
                        0 <= at(iteration, i);
                        at(iteration, i) < at(iteration, capacity);
                        0 <= capacity;
                    }
                }
                close_invariants();
            } else {
                branch then {
                    contradiction(occupied[i] == 0);
                } else {
                    step();
                }
                step();
                have 0 <= i;
                have i <= capacity;
                let run = fold(arena_scan(data, occupied, capacity), {
                    lo: i, hi: i
                });
                have 0 <= at(iteration, i) by {
                    assumption();
                }
                have 0 <= capacity - at(iteration, i) - 1 by {
                    arithmetic() using {
                        0 <= at(iteration, i);
                        at(iteration, i) < at(iteration, capacity);
                        0 <= capacity;
                    }
                }
                have capacity - at(iteration, i) - 1
                    < capacity - at(iteration, i) by {
                    arithmetic() using {
                        0 <= at(iteration, i);
                        at(iteration, i) < at(iteration, capacity);
                        0 <= capacity;
                    }
                }
                close_invariants();
            }
        }
    }
    let { lo: run_lo, hi: run_hi } = unfold(run);
    fold(arena_cells(data, occupied, capacity));
    execute();
    simp();
}
```

```expect
pass
```
