# A heap load after a possibly overlapping store uses explicit preservation

The proof splits allocation failure and the two store-alias cases. When `u`
is nonzero, it establishes separation of `buf[u]` from `buf[0]`, then uses
`statement(5).footprint` and a transport certificate to preserve the earlier
`3`. No memory-history recovery is needed.

The `separation::subrange` law derives containment in `buf[1..4]` from
explicit arithmetic bounds, without enumerating the possible indices.
Both original functions and contracts are unchanged.

```c filename=a_heap_load_after_a_store_that_may_write_its_cell_splits.c
int32 read_back(int32 u) {
    int32 r;
    int32* buf;
    buf = malloc(16);
    if (buf == 0) {
        return 0;
    }
    buf[0] = 3;
    buf[u] = 7;
    r = buf[0];
    free(buf);
    return r;
}

int32 read_back_stepped(int32 u) {
    int32 r;
    int32* buf;
    buf = malloc(16);
    if (buf == 0) {
        return 0;
    }
    buf[0] = 3;
    buf[u] = 7;
    r = buf[0];
    free(buf);
    return r;
}
```

```click
import click::separation;
verifying "a_heap_load_after_a_store_that_may_write_its_cell_splits.c";

int32 read_back(int32 u) {
    requires 0 <= u;
    requires u < 4;
    ensures result == 0 or u != 0 or result == 7;
    ensures result == 0 or u == 0 or result == 3;
} by {
    step(); step(); step();
    if buf == 0 {
    } else {
        step_until(statement(5));
        have buf[0] == 3 by solve();
        mark before_store;
        step();
        if u == 0 {
            step_until(function.exit);
        } else {
            have 1 <= u by { solve() using { 0 <= u; u != 0; }; }
            have separate(memory(buf[1..4]), memory(buf[0..1])) by assumption();
            have u <= ((u + 1) as int32) by { solve() using { 1 <= u; u < 4; }; }
            have ((u + 1) as int32) <= 4 by { solve() using { 1 <= u; u < 4; }; }
            have contains(memory(buf[1..4]), memory(buf[u..u + 1])) by {
                apply(separation::subrange(buf, 1, 4, u, u + 1)) using {
                    1 <= u; u <= ((u + 1) as int32); ((u + 1) as int32) <= 4;
                };
            }
            have contains(memory(buf[0..1]), memory(buf[0])) by { normalize(); }
            have separate(memory(buf[u..u + 1]), memory(buf[0])) by {
                apply(separation::restrict(memory(buf[1..4]), memory(buf[0..1]),
                    memory(buf[u..u + 1]), memory(buf[0]))) using {
                    separate(memory(buf[1..4]), memory(buf[0..1]));
                    contains(memory(buf[1..4]), memory(buf[u..u + 1]));
                    contains(memory(buf[0..1]), memory(buf[0]));
                };
            }
            have contains(memory(buf[u..u + 1]), memory(buf[u])) by { normalize(); }
            have contains(memory(buf[0]), memory(buf[0])) by { normalize(); }
            have separate(memory(buf[u]), memory(buf[0])) by {
                apply(separation::restrict(memory(buf[u..u + 1]), memory(buf[0]),
                    memory(buf[u]), memory(buf[0]))) using {
                    separate(memory(buf[u..u + 1]), memory(buf[0]));
                    contains(memory(buf[u..u + 1]), memory(buf[u]));
                    contains(memory(buf[0]), memory(buf[0]));
                };
            }
            have separate(statement(5).footprint, memory(buf[0])) by {
                normalize() using { separate(memory(buf[u]), memory(buf[0])); };
            }
            have buf[0] == at(before_store, buf[0]) by {
                transport_certificate {
                    premise 0: separate(statement(5).footprint, memory(buf[0]))
                        => separate(statement(5).footprint, memory(buf[0]));
                    preserve 0 => buf[0] == at(before_store, buf[0]);
                    conclusion 1;
                }
            }
            have buf[0] == 3 by solve();
            step_until(function.exit);
        }
    }
}

int32 read_back_stepped(int32 u) {
    requires 0 <= u;
    requires u < 4;
    ensures result == 0 or u != 0 or result == 7;
    ensures result == 0 or u == 0 or result == 3;
} by {
    step(); step(); step();
    if buf == 0 {
    } else {
        step_until(statement(5));
        have buf[0] == 3 by solve();
        mark before_store;
        step();
        if u == 0 {
            step_until(function.exit);
        } else {
            have 1 <= u by { solve() using { 0 <= u; u != 0; }; }
            have separate(memory(buf[1..4]), memory(buf[0..1])) by assumption();
            have u <= ((u + 1) as int32) by { solve() using { 1 <= u; u < 4; }; }
            have ((u + 1) as int32) <= 4 by { solve() using { 1 <= u; u < 4; }; }
            have contains(memory(buf[1..4]), memory(buf[u..u + 1])) by {
                apply(separation::subrange(buf, 1, 4, u, u + 1)) using {
                    1 <= u; u <= ((u + 1) as int32); ((u + 1) as int32) <= 4;
                };
            }
            have contains(memory(buf[0..1]), memory(buf[0])) by { normalize(); }
            have separate(memory(buf[u..u + 1]), memory(buf[0])) by {
                apply(separation::restrict(memory(buf[1..4]), memory(buf[0..1]),
                    memory(buf[u..u + 1]), memory(buf[0]))) using {
                    separate(memory(buf[1..4]), memory(buf[0..1]));
                    contains(memory(buf[1..4]), memory(buf[u..u + 1]));
                    contains(memory(buf[0..1]), memory(buf[0]));
                };
            }
            have contains(memory(buf[u..u + 1]), memory(buf[u])) by { normalize(); }
            have contains(memory(buf[0]), memory(buf[0])) by { normalize(); }
            have separate(memory(buf[u]), memory(buf[0])) by {
                apply(separation::restrict(memory(buf[u..u + 1]), memory(buf[0]),
                    memory(buf[u]), memory(buf[0]))) using {
                    separate(memory(buf[u..u + 1]), memory(buf[0]));
                    contains(memory(buf[u..u + 1]), memory(buf[u]));
                    contains(memory(buf[0]), memory(buf[0]));
                };
            }
            have separate(statement(5).footprint, memory(buf[0])) by {
                normalize() using { separate(memory(buf[u]), memory(buf[0])); };
            }
            have buf[0] == at(before_store, buf[0]) by {
                transport_certificate {
                    premise 0: separate(statement(5).footprint, memory(buf[0]))
                        => separate(statement(5).footprint, memory(buf[0]));
                    preserve 0 => buf[0] == at(before_store, buf[0]);
                    conclusion 1;
                }
            }
            have buf[0] == 3 by solve();
            step_until(function.exit);
        }
    }
}

```

```expect
pass
```
