# A call step names its callee, not its call

A call step's map fills in the callee's contract, so the step names that
contract, `step(increment, { first: c })`, and takes the call's arguments
from the call at the frontier. Restating the call,
`step(increment(state), { first: c })`, is retired, and so is a map with no
name, `step({ first: c })`; each is refused with the form to write.

```c filename=a_call_step_names_its_callee_not_its_call.c
void increment(int32* state) { }
void caller(int32* state) { increment(state); }
```

```click
verifying "a_call_step_names_its_callee_not_its_call.c";

resource Counter() { field revision: int32; }

void increment(int32* state) {
    owns first: Counter();
}

void caller(int32* state) {
    owns c: Counter();
} by {
    step(increment(state), { first: c });
}
```

```expect
fail: `step(increment(...), { ... })` is retired: write `step(increment, { ... })`; the call's arguments come from the call at the frontier
```
