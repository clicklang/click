# Callback contract lookup does not consume checked pointer equality

Soundness: incomplete. A valid callback call is rejected when an argument is
proved equal to a constant callback table. No false acceptance is known.

The fenced C and Click blocks below are the reduced reproduction.
Its target function and execution theorem check independently; normal verification
fails at `have Invoke(cb->call) by { assumption(); }`. The same failure blocks
`CopySizedStructure` dispatch in the rbtree augmentation table prototype.

The checked read bridge is now repaired: function reads retain their exact
producer definitions, expression composition preserves certified load metadata
even when the defining equation is redundant, and statement publication carries
the checked read evidence into the following proof context. The complete copy
proof in `mdtests/function_pointer_read_uses_checked_table_alias.md` verifies;
its missing-alias counterpart is refused. Kernel regressions cover withdrawal,
branch isolation, changed snapshots, and absence of additional read permission.

In the reproduction below, adding
`have cb->call == (&table)->call by { assumption(); }` after the load now passes.
The trace prints the admitted equality between the defining read and the
initialized function. The following `Invoke(cb->call)` obligation still fails:
predicate assumption requires exact arguments, and callback-contract lookup is
indexed by the exact pointer spelling rather than its checked equality class.
Trying to transport it explicitly with
`rewrite(cb->call == (&table)->call)` fails with
"`rewrite` pointer equality expects a condition goal".

The remaining issue is contract-fact lookup/transport, rather than missing read
evidence. A solution must preserve contract state, signature, branch scope, and
withdrawal, use selected equality evidence without scanning unrelated contracts,
and verify the public callback call and rbtree dispatcher. The choice of how to
extend this existing exact lookup needs discussion under AGENTS.md. Remove this
file once that remaining reproduction and its regressions pass.

## Reproduction

Normal verification should pass, including the target function and execution
theorem. It currently rejects the `Invoke(cb->call)` obligation.

```c filename=callbacks.c
struct callbacks { void (*call)(int *p); };
static void target(int *p) { }
static const struct callbacks table = { .call = target };
void concrete(int *p) {
 const struct callbacks *cb = &table;
 cb->call(p);
}
void symbolic(int *p, const struct callbacks *cb) { cb->call(p); }
```

```click
verifying "callbacks.c";
contract void Invoke(int32* p) { ensures true; }
void target(int32* p) { ensures true; } by { execute(); simp(); }
theorem target_has_contract()
executes target(int32* p) {
    ensures Invoke(&target) by { execute(); simp(); }
}
void symbolic(int32* p, const struct callbacks* cb) {
    requires cb == &table;
    views cb->call;
    ensures true;
} by {
    step();
    have cb == &table by { assumption(); }
    step();
    apply(target_has_contract());
    have Invoke(cb->call) by { assumption(); }
    step(Invoke);
    execute(); simp();
}
```

```expect
pass
```
