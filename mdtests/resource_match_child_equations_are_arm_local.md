# Resource child field equations are local to each match arm

Both arms may reuse a child name and equate its value with a different parent
field. Later facts in an arm use that arm's alias; aliases never cross arms.

```c filename=resource_match_child_equations.c
void keep(int32* p) {}
```

```click
verifying "resource_match_child_equations.c";
spec enum Phase { Before, After }
resource cell(p: int32*) {
    field value: int32;
    owns p[0..1];
    fact p[0] == value;
}
resource holder(p: int32*) {
    field phase: Phase;
    field first: int32;
    field second: int32;
    match phase {
        Phase::Before => {
            owns child: cell(p);
            fact child.value == first;
            fact child.value >= 0;
        },
        Phase::After => {
            owns child: cell(p);
            fact child.value == second;
            fact child.value >= 1;
        },
    }
}
void keep(int32* p) {
    owns state: holder(p);
    ensures state.phase == old(state.phase);
    ensures state.first == old(state.first);
    ensures state.second == old(state.second);
} by {
    match state.phase {
        Phase::Before => {
            let { first: first, second: second, child: child } = unfold(state);
            have first >= 0 by { assumption(); }
            unfold(child); execute();
            let child = fold(cell(p), { value: first });
            let state = fold(holder(p), { phase: Phase::Before, first: first, second: second }, { child: child });
            simp();
        },
        Phase::After => {
            let { first: first, second: second, child: child } = unfold(state);
            have second >= 1 by { assumption(); }
            unfold(child); execute();
            let child = fold(cell(p), { value: second });
            let state = fold(holder(p), { phase: Phase::After, first: first, second: second }, { child: child });
            simp();
        },
    }
}
```

```expect
pass
```
