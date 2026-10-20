# a call step checks its written arguments

`step(callee(args), { ... })` states the call it steps, so each written
argument must equal the call's own argument at the pre-state. Here the C call
passes `state`, the step writes `0`, and nothing shows `state == 0`.

```c filename=a_call_step_checks_its_written_arguments.c
void increment(int *state) { }
void run(int *state) { increment(state); }
```

```click
verifying "a_call_step_checks_its_written_arguments.c";

resource Counter() { field revision: int32; }

void increment(int32* state) {
    owns first: Counter();
} by {
    execute();
}

void run(int32* state) {
    owns c: Counter();
} by {
    step(increment(0), { first: c });
    execute();
}
```

```expect
fail: argument 1 differs from the call's
```
