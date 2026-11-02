# A loop binder's footprint includes the memory its instance owns

`mark_run` marks the cells `[start, end)` of an occupancy map through a
loop that owns a field-bearing `window` instance, and the window owns the
whole map. After the loop the proof tries to carry the value that
`occupied[start]` had before the loop across it with `transport`, which
would let it conclude `start < 0` from `0 <= start` once the loop's own
store is known.

A loop that declares resources havocs the memory those resources own. The
footprint was computed by expanding composites only, and an owned
field-bearing instance (or an iterated ownership fact) contributed nothing,
so the loop was summarized as writing none of the map and the transport
succeeded. The footprint now opens the instance one body layer at its own
fields, as `unfold` does, and an iterated fact contributes the span of the
elements it could hold, so the transport has no frame evidence for a cell
the loop may write.

```c filename=loop_binder_instance_footprint_includes_its_memory.c
void mark_run(int32* occupied, int32 capacity, int32 start, int32 end) {
    int32 i;
    occupied[start] = 0;
    i = start;
    while (i < end) {
        occupied[i] = 1;
        i = i + 1;
    }
}
```

```click
resource window(occupied: int32*, capacity: int32, start: int32, end: int32) {
    field next: int32;
    owns occupied[0..capacity];
    fact 0 <= start;
    fact start <= next;
    fact next <= end;
    fact end <= capacity;
    fact forall (k: int32) {
        start <= k and k < next implies occupied[k] == 1
    };
}

verifying "loop_binder_instance_footprint_includes_its_memory.c";

void mark_run(int32* occupied, int32 capacity, int32 start, int32 end) {
    consumes w: window(occupied, capacity, start, end);
    requires w.next == start;
    requires start < end;
    ensures start < 0;
} by {
    let { next: n0 } = unfold(w);
    have 0 <= start by solve();
    have start < capacity by solve();
    step();
    step();
    have occupied[start] == 0 by solve();
    step();
    let w = fold(window(occupied, capacity, start, end), { next: start });
    mark pre;
    loop {
        owns w: window(occupied, capacity, start, end);
        invariant w.next == i;
        decreases end - i;
        initialize by solve();
        preserve by {
            let { next: m } = unfold(w);
            have m == i by solve();
            have i < end by solve();
            have start <= m by solve();
            have 0 <= m;
            have 0 <= i by {
                rewrite(i == m);
                assumption();
            }
            have i < capacity;
            mark opened;
            step();
            step();
            have forall (k: int32) {
                start <= k and to_integer(k) < to_integer(at(opened, i) + 1) implies occupied[k] == 1
            } by {
                intro();
                intro();
                extract(to_integer(k) < to_integer(at(opened, i) + 1));
                if k < at(opened, i) {
                    have k < m by solve();
                    have at(opened, occupied[k]) == 1 by {
                        instantiate(forall (j: int32) {
                            at(opened, start) <= at(opened, j) and
                                at(opened, j) < at(opened, m) implies
                                at(opened, occupied[j]) == at(opened, 1)
                        }, k) using {
                            start <= k;
                            k < m;
                        };
                        assumption();
                    }
                    have 0 <= k by solve();
                    transport(at(opened, occupied[k]) == 1, occupied[k] == 1) using {
                        at(opened, occupied[k]) == 1;
                        k < at(opened, i);
                        0 <= k;
                        0 <= at(opened, i);
                        at(opened, i) < capacity;
                    };
                } else {
                    have k <= at(opened, i);
                    have k == at(opened, i);
                    rewrite(k == at(opened, i));
                    normalize();
                }
            }
            have start <= at(opened, i) by {
                rewrite(at(opened, i) == m);
                assumption();
            }
            have to_integer(start) <= to_integer(at(opened, i) + 1);
            have to_integer(at(opened, i) + 1) <= to_integer(end);
            let w = fold(window(occupied, capacity, start, end), {
                next: at(opened, i) + 1
            });
            have 0 <= to_integer(end - at(opened, i) - 1) by {
                solve() using {
                    at(opened, i) < end;
                    0 <= at(opened, i);
                    end <= capacity;
                };
            }
            have to_integer(end - at(opened, i) - 1) < to_integer(end - at(opened, i)) by {
                solve() using {
                    at(opened, i) < end;
                    0 <= at(opened, i);
                    end <= capacity;
                };
            }
        }
    }
    let { next: n } = unfold(w);
    have occupied[start] == at(pre, occupied[start]) by {
        transport(
            at(pre, occupied[start]) == at(pre, occupied[start]),
            occupied[start] == at(pre, occupied[start])
        ) using {
            0 <= start;
            start < capacity;
        };
    }
    have n == i by solve();
    have n <= end by solve();
    have not (n < end) by {
        rewrite(n == i);
        assumption();
    }
    have n == end;
    have start < n by {
        rewrite(n == end);
        assumption();
    }
    have start <= start by normalize();
    have occupied[start] == 1 by {
        instantiate(forall (j: int32) {
            start <= j and j < n implies occupied[j] == 1
        }, start) using {
            start <= start;
            start < n;
        };
        assumption();
    }
    have at(pre, occupied[start]) == 0 by solve();
    have occupied[start] == 0 by {
        rewrite(occupied[start] == at(pre, occupied[start]));
        assumption();
    }
    have start < 0 by {
        contradiction(occupied[start] == 1);
    }
}
```

```expect
fail: `transport using` found no frame evidence
```
