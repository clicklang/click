# A quantified frame over a large constant range exhausts the load registry

Soundness: not soundness-adjacent. The false claim is refused, by a panic
rather than a diagnostic, so nothing false verifies; the defect is an
unbounded failure and a crash.

Violated invariant: a false quantified claim over a range fails promptly
with a diagnostic, and work scales with the proof, not with the range's
element count.

Reproduction (release build of master at 93bc0b8, 2026-10-14; about 43 s to the panic):

```c
int32 untouched_element(int32* a) {
    unsigned char* b;
    b = (unsigned char*)(void*) a;
    b[5] = 7;
    return a[2];
}
```

```click
int32 untouched_element(int32* a) {
    owns a[0..1000000];
    ensures result == old(a[2]);
    ensures (0..1000000).all(|k| { a[k] == old(a[k]) });
} by { execute(); simp(); }
```

Expected: a prompt failure of the second (false) claim. Actual: about 47 s,
then a panic at `src/kernel/eval/memory_loads.rs:3349`: "load-variable
registry capacity exhausted ... minted 1000000 distinct load identities".
The closing search appears to mint a
load identity per element of the seeded constant run.

Acceptance criteria:

- The reproduction fails within a second with an ordinary refusal of the
  `all` claim, without minting a load identity per element.
- A regression mdtest keeps the original pattern (a byte store through a
  `unsigned char*` view of an owned `int32` range, and a whole-range
  `all` frame over a large constant range).
