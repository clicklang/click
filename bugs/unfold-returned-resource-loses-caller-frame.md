# Unfolding a returned resource loses an untouched caller cell

A call that consumes and produces a named resource preserves separately owned
caller cells. Opening the returned resource must preserve that framing fact: an
unfold names existing storage and does not execute a C write.

## Reproduction

```c
void keep(int32 *anchor) {}
void call(int32 *anchor, int32 *other) { keep(anchor); }
```

Save the C as `cell.c`, with this sidecar:

```click
verifying "cell.c";
resource cell(p: int32*) { field tag: int32; owns *p; }
void keep(int32* anchor) {
    consumes a: cell(anchor);
    produces b: cell(anchor);
} by {
    unfold(a);
    let b = fold(cell(anchor), { tag: old(a.tag) });
    execute(); simp();
}
void call(int32* anchor, int32* other) {
    consumes c: cell(anchor);
    owns *other;
    produces *anchor;
    ensures *other == old(*other);
} by {
    let { b: d } = step(keep(anchor), { a: c });
    unfold(d);
    have *other == old(*other) by { simp(); }
    execute(); simp();
}
```

The `have` fails at `simp`. Moving it immediately before `unfold(d)` passes.
An explicit `have separate(memory(*anchor), memory(*other)) by { assumption(); }`
after the unfold succeeds but does not repair the following equality proof.
The behavior also reproduces with a produced resource that changes pointer
arguments, under both a fresh output name and a reused consumed name.

## Acceptance

The sidecar verifies and audits without added framing bookkeeping. Keep a
negative regression that rejects an actual write to the supposedly unchanged
cell. Preserve initialization checks and checked memory-DAG evidence, and do
not introduce whole-context scans or pairwise resource enumeration.
