# Named contract output bindings cannot prove a false C result

```c filename=calls.c
int32 repair(int32 *p) { *p = 1; return 0; }
void direct(int32 *x) { if (repair(x)) return; }
void indirect(int32 (*callback)(int32*), int32 *x) { if (callback(x)) return; }
```

```click
verifying "calls.c";
resource Dirty(p: int32*) { field value: int32; owns p[0..1]; fact p[0] == value; }
resource Ready(p: int32*) { field value: int32; owns p[0..1]; fact p[0] == value; }
contract int32 Repair(int32* p) {
    consumes input: Dirty(p);
    produces output: Ready(p);
    ensures output.value == 1;
    ensures result == 0;
}
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
    have status == 1 by { assumption(); }
    unfold(done);
    have x[0] == 1 by { assumption(); }
    let done = fold(Ready(x), { value: 1 });
    execute();
    simp();
}
```

```expect
fail: `assumption` requires the current goal as an available semantic fact
```
