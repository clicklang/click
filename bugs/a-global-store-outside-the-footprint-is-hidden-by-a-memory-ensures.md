# A global store outside the footprint is hidden by an `ensures` that reads memory

Soundness: not soundness. The function is refused either way; only the
diagnostic is wrong, and it names no cause.

A store to file-scope storage that the contract does not own is reported
at finalization: "write to storage outside the owned footprint". When the
contract also has an `ensures` that reads memory, the claim proof fails
first, at the implicit closer, with no usable reason:

```text
`f.contract` path 0, tactic 1
checked outcome `simp` did not retain a complete transition for every pending claim
```

The message names no claim, no cell and no store, so the reader cannot tell
that the store is the problem. The same shape through a pointer parameter
(`owns p->second;` and a store to `p->first`) reports the store correctly
at `execute()` ("missing resource fact `owns p->first`").

Reproduced on master `256fa76` (release build) with a written `ensures`:

```c
struct pair {
    int32 first;
    int32 second;
};

struct pair shared;

int32 f() {
    shared.first = 9;
    return 0;
}
```

```click
verifying "a.c";

int32 f() {
    owns shared.second;
    ensures result == 0;
    ensures shared.second == old(shared.second);
}
```

Without the second `ensures` the refusal is "write to storage outside the
owned footprint", as `mdtests/static_struct_field_footprint_rejected.md`
expects.

Acceptance criteria:

- The reproduction is refused with the footprint message naming
  `shared.first`, or at the store, as the pointer-parameter form is.
- A regression keeps the reproduction's original pattern, the written
  `ensures` beside the store to `shared.first`.
