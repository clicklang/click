# A named-contract step hint introduces a produced handle with let

`Repair` consumes `input` and produces `output`. A bare `step(Repair)` is
refused, and its hint names the spelling that verifies: the map supplies
only `input`, and the `let` pattern introduces `output`.

```c filename=a_named_contract_step_hint_introduces_a_produced_handle.c
void indirect(int (*callback)(int *), int *x) { callback(x); }
```

```click
verifying "a_named_contract_step_hint_introduces_a_produced_handle.c";

resource Dirty(p: int32*) { field value: int32; owns p[0..1]; fact p[0] == value; }
resource Ready(p: int32*) { field value: int32; owns p[0..1]; fact p[0] == value; }

contract int32 Repair(int32* p) {
    consumes input: Dirty(p);
    produces output: Ready(p);
    ensures output.value == 1;
}

void indirect(int32 (*callback)(int32*), int32* x) {
    requires Repair(callback);
    consumes dirty: Dirty(x);
    produces done: Ready(x);
    ensures done.value == 1;
} by {
    step(Repair);
    execute();
    simp();
}
```

```expect
fail: write `let { output: ... } = step(Repair, { input: ... })`
```
