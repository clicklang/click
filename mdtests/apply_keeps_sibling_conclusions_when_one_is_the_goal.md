# apply keeps every conclusion when one of them is the goal

`three_bounds` guarantees `x >= 0`, `x <= 10`, and `x != 11`. Each proof below
applies it where one of those guarantees is the goal itself, and then needs a
sibling guarantee: as the requirement of a second theorem, as a listed
`using` premise, or restated by `have`. An application adds every guarantee
of its theorem, whichever one the goal happens to be.

```click
predicate small(x: int32) {
    x >= 0 and x <= 10
}

theorem three_bounds(x: int32) {
    requires small(x);

    ensures x >= 0 by {
        unfold(small);
        simp();
    }

    ensures x <= 10 by {
        unfold(small);
        simp();
    }

    ensures x != 11 by {
        unfold(small);
        simp();
    }
}

theorem needs_upper(x: int32) {
    requires x <= 10;

    ensures x <= 20 by {
        simp();
    }
}

theorem needs_both_siblings(x: int32) {
    requires x >= 0;
    requires x != 11;

    ensures x >= 0 by {
        assumption();
    }
}

theorem goal_is_the_first_conclusion(x: int32) {
    requires small(x);

    ensures x >= 0 by {
        apply(three_bounds(x));
        apply(needs_upper(x));
        assumption();
    }
}

theorem goal_is_the_middle_conclusion(x: int32) {
    requires small(x);

    ensures x <= 10 by {
        apply(three_bounds(x)) using {
            small(x);
        }
        apply(needs_both_siblings(x)) using {
            x >= 0;
            x != 11;
        }
        assumption();
    }
}

theorem a_sibling_conclusion_is_restated(x: int32) {
    requires small(x);

    ensures x != 11 by {
        apply(three_bounds(x));
        have x <= 10 by {
            assumption();
        }
        assumption();
    }
}

theorem goal_is_no_conclusion(x: int32) {
    requires small(x);

    ensures x <= 20 by {
        apply(three_bounds(x));
        apply(needs_upper(x));
        assumption();
    }
}
```

```expect
pass
```
