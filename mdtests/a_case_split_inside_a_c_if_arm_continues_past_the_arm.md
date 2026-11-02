# A case split inside a C `if` arm continues past the arm

The implicit tail plans every path to function exit. A C `if` it enters as a
`branch` bounds each arm at the `if`'s shared continuation, and a path that
reaches that boundary continues privately into the continuation through the
branch's split. A case split inside the arm did not: its cases ran as
top-level execution, so the first step past the arm, the `return`, failed as
running off the end of the branch body. Two such splits are a load that may
read an earlier store's cell (`loc[0]` after `loc[u] = 7`, in `read_back`)
and a short-circuit condition (`0 <= x && x < 4`, whose arm holds the C `if`
in `nested`). Each case now runs under the chain of arms it is nested in and
escapes exactly as many of them as it finishes, as a focused execution does.

```c filename=a_case_split_inside_a_c_if_arm_continues_past_the_arm.c
int32 read_back(int32 u, int32 c) {
    int32 r;
    int32 loc[4];
    loc[0] = 3;
    loc[1] = 3;
    loc[u] = 7;
    r = 0;
    if (c) {
        r = loc[0];
    }
    return r;
}

int32 nested(int32 x, int32 y) {
    int32 r;
    r = 0;
    if (0 <= x && x < 4) {
        if (y) {
            r = 1;
        }
    }
    return r;
}
```

```click
import click::separation;
verifying "a_case_split_inside_a_c_if_arm_continues_past_the_arm.c";

int32 read_back(int32 u, int32 c) {
    requires 0 <= u;
    requires u < 2;
    ensures result == 0 or result == 3 or result == 7;
} by {
    step(); step(); step(); step();
    have loc[0] == 3 by { normalize(); }
    mark before_store;
    step();
    have loc[u] == 7 by { normalize(); }
    have loc[0] == 3 or loc[0] == 7 by {
        if u == 0 {
            have loc[0] == 7 by { normalize() using { loc[u] == 7; u == 0; }; }
            assumption();
        } else {
            have separate(memory(loc[u]), memory(loc[0])) by {
                apply(separation::elements(loc, u, 0)) using { u != 0; };
            }
            have separate(statement(4).footprint, memory(loc[0])) by {
                normalize() using { separate(memory(loc[u]), memory(loc[0])); };
            }
            have loc[0] == at(before_store, loc[0]) by {
                transport_certificate {
                    premise 0: separate(statement(4).footprint, memory(loc[0]))
                        => separate(statement(4).footprint, memory(loc[0]));
                    preserve 0 => loc[0] == at(before_store, loc[0]);
                    conclusion 1;
                }
            }
            have loc[0] == 3 by { normalize() using { loc[0] == at(before_store, loc[0]); at(before_store, loc[0]) == 3; }; }
            assumption();
        }
    }
    mark stored;
    step();
    have loc[0] == at(stored, loc[0]) by { normalize(); }
    have loc[0] == 3 or loc[0] == 7 by { solve(); }
}

int32 nested(int32 x, int32 y) {
    ensures result == 0 or result == 1;
}
```

```expect
pass
```
