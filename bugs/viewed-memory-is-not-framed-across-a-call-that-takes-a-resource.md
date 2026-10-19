# Viewed memory is not framed across a call that takes a user resource

Soundness: incomplete. A true claim is refused; the frame that is lost is
memory the caller only views, so no false claim is accepted.

A caller that holds `views *cell` and does not pass it to a callee keeps it
unchanged across the call: the callee cannot write memory another holder views.
Click keeps it when the callee's contract names only memory, but not when the
callee consumes and produces a user-declared resource. The call's effect is then
recorded as "may write an unbounded range at an unknown base". Its retained
frame lists only the caller's owned memory, not its viewed memory. A read of
`*cell` before the call no longer equals `*cell` after it. With `owns *cell` in
place of `views *cell`, the same proof verifies.

Reproduction (measured on master `2095c2325`, the merge of #1554):

```c
struct node { int value; struct node *next; };
void touch(struct node *node) {
}
int keep(int *cell) {
    int value = *cell;
    touch(0);
    return value;
}
```

```click
verifying "views.c";

resource list_at(p: struct node*) {
    if p != 0 {
        owns *p;
        owns list_at(p->next);
    }
}

void touch(struct node* node) {
    owns list_at(node);
} by {
    execute();
    simp();
}

int32 keep(int32* cell) {
    views *cell;
    ensures result == *cell;
} by {
    fold(list_at(0));
    execute();
    simp();
}
```

`keep.ensures_0` fails: "`cell[0]` may have changed since the outcome state:
the call in between may have written it, and the ranges it may write are not
shown separate from it". `--trace-proof keep` shows the call effect
`may write [memory(value#5[Int32:0..2147483647], stride=1)]` with
`caller-owned frame retained [owns memory(value#4...)]`, the local `value`
only. A resource with fields (`field items: List<int32>`, consumed and
produced) fails the same way. A callee whose contract names no resource keeps
the viewed cell.

Acceptance criteria:

- The reproduction verifies with `views *cell`, and a false variant
  (`ensures result == *cell + 1`) is still refused.
- Viewed memory the caller does not pass to the callee is retained in the
  call's frame, as owned memory is. A regression covers a resource-taking
  callee, with fields and without.
