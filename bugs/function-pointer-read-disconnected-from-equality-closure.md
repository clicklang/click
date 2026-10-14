# Function-pointer reads omit the shared checked read bridge

Soundness: incomplete. A valid callback call is rejected when an argument is
proved equal to a constant callback table. No false acceptance is known.

The fenced C and Click blocks below are the reduced reproduction.
Its target function and execution theorem check independently; normal verification
fails at `have Invoke(cb->call) by { assumption(); }`. The same failure blocks
`CopySizedStructure` dispatch in the rbtree augmentation table prototype.

The trace shows the available `cb == &table` fact, the original initialized
function address still stored in the load's defining memory, and a separate
symbolic function-pointer read value. The contract is known for the initialized
function address, but lookup does not connect it to the checked read.

`cell_run_value` constructs function-pointer cells with canonical load variables,
but does not register their typed pointer read definitions. The checked read
candidate filter also omits `PointerBlock::FunctionSymbolic`. Object-pointer
reads already use this producer/checked evidence path and address-class lookup.

Restoring those two omitted cases alone did not discharge the obligation.
A further experiment widening the observed-read recorder also did not suffice;
no verifier fix is included. Investigate which checked binding reaches the
proof context and equality graph before extending any rule. A fix must
verify the public reproduction and rbtree dispatch, preserve branch scope and
withdrawal, distinguish changed snapshots, and grant no read permission merely
because the definition is retained. Remove this file when the fix and regressions
land.

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
