# A mark made in an outer loop body is unknown inside an inner loop

A `mark name;` records the proof state where it is written, and `at(name, e)`
reads `e` there for the rest of the proof. Inside a nested `loop` clause the
mark is refused as unknown, in the inner loop's body proof and in its
invariants, although the outer body's own steps before and after the inner
loop can name it.

```c
int count(void) {
    int i = 0;
    while (i < 3) {
        int j = 0;
        while (j < 2) {
            j = j + 1;
        }
        i = i + 1;
    }
    return i;
}
```

```click
verifying "r.c";
int32 count() {
    ensures result == result;
} by {
    execute_until(loop(0));
    loop {
        decreases 3 - i;
        invariant i <= 3;
        preserve by {
            mark outer_head;
            have at(outer_head, i) < 3 by { simp(); }
            execute_until(loop(1));
            loop {
                decreases 2 - j;
                invariant j <= 2;
                invariant i <= 3;
                preserve by {
                    have at(outer_head, i) < 3 by { assumption(); }
                    execute_until(back_edge());
                    close_invariants();
                }
            }
            execute_until(back_edge());
            close_invariants();
        }
    }
    execute(); simp();
}
```

`click verify` reports, at the inner `have`:

```
could not lower `have` proposition: unknown proof mark `outer_head`; add
`mark outer_head;` after the proof reaches that frontier
```

An invariant of the inner loop that names the mark is refused with
"proof-local mark `outer_head` is available only in an execution proof".

## Violated invariant

A mark names one fixed state of the enclosing proof. The state it names does
not change while the inner loop runs, so a fact about it is as meaningful
inside the inner loop as after it. The inner loop already reads enclosing
state through `at(loop(1).entry, e)` and `old(e)`.

## Why it matters

A value fixed before the inner loop, such as the outer iterator's count at
the head of the outer iteration, has no spelling inside the inner loop. The
general Adler-32 proof (`design/charon-trial/adler2/general-compute.click`)
needed the position of a chunk in the whole input there and could not state
it; it now relies on the kernel covering a callee's window through the view
the inner loop holds.

## Acceptance criteria

- The reproduction above verifies: `at(outer_head, i)` is accepted in the
  inner loop's body proof.
- Either an inner loop's `invariant` may name an enclosing mark, or the
  refusal says that an invariant cannot and names `at(loop(n).entry, e)` as
  the spelling to use.
- A mark made inside the inner loop body is still unknown outside it.
