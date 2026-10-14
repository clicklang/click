# A post-return unfold of a call-produced instance is refused

Soundness: incomplete. Click refuses a valid proof; the same steps verify
when the `unfold` is moved before `execute()`, and an unfold after return of
an instance the function consumed (rather than one a call produced) also
verifies. No false acceptance is known: both refusals are in return
certification and claim certification, which only reject.

Violated invariant: after execution reaches function exit, unfolding a held
named instance is a checked resource exchange on the returned state wherever
the instance came from. A later fold and the contract's claims are certified
against the same returned snapshot the proof used.

Reproduction (release build of `r2fix`, 2026-10-14). The callee produces an
instance; the caller unfolds it after its own return and folds its output:

````md
```c filename=s.c
struct node { struct node* left; };
struct root { struct node* top; };

void relink(struct root* r, struct node* n) {
    r->top = n;
}

int32 pick(struct root* r, struct node* n) {
    struct node* t = n;
    relink(r, t);
    return 0;
}
```

```click
spec enum Ctx { Top, Other }
resource at(child: struct node*, r: struct root*) {
    field model: Ctx;
    match model {
        Ctx::Top => {
            owns r->top;
            fact r != 0;
            fact r->top == child;
        },
        Ctx::Other => {
            owns r->top;
        },
    }
}
resource out(r: struct root*) {
    field model: int32;
    owns r->top;
    fact r != 0;
}
verifying "s.c";
void relink(struct root* r, struct node* n) {
    consumes before: at(0, r);
    requires before.model == Ctx::Top;
    produces after: at(n, r);
    ensures after.model == Ctx::Top;
} by {
    unfold(before);
    execute();
    let after = fold(at(n, r), { model: Ctx::Top });
    simp();
}
int32 pick(struct root* r, struct node* n) {
    consumes c: at(0, r);
    requires c.model == Ctx::Top;
    produces o: out(r);
    ensures o.model == 0;
} by {
    step();
    step();
    let { after: c } = step(relink(r, t), { before: c });
    execute();
    unfold(c);
    let o = fold(out(r), { model: 0 });
    simp();
}
```
````

```text
proof error:
  instance rewrite introduced an unchecked fact

tactic@60:
  unfold(c);
```

The unchecked fact is a `CMemoryLoadable` of the unfolded `r->top` cell over
the returned snapshot (memory construction `LocalLifetimeEnded`). The
kernel's recheck in `CheckedResourceRewrite::check_with_children`
(`src/kernel/proof/execution.rs`) computes the exchange from the retained
C-body return state, so the loadability fact the surface published over the
outcome snapshot is not in its allowed set.

Without the local `t` (`relink(r, n); return 0;`, the proof starting at the
`step(relink(r, n), ...)`), the unfold is accepted but the contract is
refused instead, even for `ensures result == 0;`:

```text
proof error:
  `pick.contract` claim Ensure(1) on path 0 has mismatched proposition completion evidence
  the proposition completion does not match the checked program state
```

That message comes from `contract_claims.rs`: the completion's memory, which
the unfold changed by naming the call-havocked cells it exposes, no longer
equals the certified path's. The two refusals may have one cause (the
post-return unfold names cells in the outcome snapshot that the retained
trace does not share); split this file if they do not.

Both verify with `unfold(c);` moved before `execute();`, and the same
post-return `unfold` of a consumed (not call-produced) instance verifies.

Found while landing the general `__rb_erase_augmented` contract
(design-review P5, R2): the leaf and immediate-successor exits unfold a
`ctx_at` or `rb_at` that `__rb_change_child` produced. They unfold it before
the final `augment->propagate` call and fold the outcome after return.

Acceptance:

- Both variants verify as mdtests that keep the post-return `unfold` of the
  call-produced instance.
- The kernel recheck stays exact: it accepts the unfold's facts because they
  are this exchange's checked facts on the returned snapshot, not by
  admitting arbitrary loadability facts.
