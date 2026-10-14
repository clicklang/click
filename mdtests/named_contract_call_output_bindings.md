# Named contract calls bind the C value and fresh resource outputs

```c filename=calls.c
int32 repair(int32 *p) { *p = 1; return 0; }
void direct(int32 *x) { if (repair(x)) return; }
void indirect(int32 (*callback)(int32*), int32 *x) { if (callback(x)) return; }
```

```click
verifying "calls.c";
import "named_contract_call_output_contracts.click";
int32 repair(int32* p) {
    consumes input: Dirty(p);
    produces output: Ready(p);
    ensures output.value == 1;
    ensures result == 0;
} by { unfold(input); execute(); let output = fold(Ready(p), { value: 1 }); simp(); }
theorem repair_contract() executes repair(int32* p) {
    ensures Repair(&repair) as { input: input, output: output } by {
        let { output: output } = step(repair(p), { input: input });
        simp();
    }
}
void direct(int32* x) {
    consumes dirty: Dirty(x);
    produces done: Ready(x);
    ensures done.value == 1;
} by {
    apply(repair_contract());
    let { result: status, output: done } = step(Repair, { input: dirty });
    have status == 0 by { assumption(); }
    unfold(done);
    have x[0] == 1 by { assumption(); }
    let done = fold(Ready(x), { value: 1 });
    execute();
    simp();
}
void indirect(int32 (*callback)(int32*), int32* x) {
    requires Repair(callback);
    consumes dirty: Dirty(x);
    produces done: Ready(x);
    ensures done.value == 1;
} by {
    let { result: status, output: done } = step(Repair, { input: dirty });
    have status == 0 by { assumption(); }
    unfold(done);
    have x[0] == 1 by { assumption(); }
    let done = fold(Ready(x), { value: 1 });
    execute();
    simp();
}
```

```expect
pass
```
