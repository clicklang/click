# A `do ... while` loop may be the first statement of a function

Entering a `do ... while` body records no evidence of its own. When the loop
was the first thing a function executed, the proof object started matching
evidence from the body alone and found no loop head left when the condition
was decided, so `auto`, `execute()`, and `step()` all failed with an internal
evidence error. The Linux kernel wraps its statement macros in
`do { ... } while (0)`, and they often open a function.

```c filename=c_do_while_first_statement.c
int32 assign(int32 v) {
    do {
        v = v + 0;
    } while (0);
    return v;
}

int32 store(int *p) {
    do {
        *p = 3;
    } while (0);
    return *p;
}

int32 executed(int32 v) {
    do {
        v = v + 0;
    } while (0);
    return v;
}

int32 stepped(int32 v) {
    do {
        v = v + 0;
    } while (0);
    return v;
}
```

```click
verifying "c_do_while_first_statement.c";

int32 assign(int32 v) {
    ensures result == v by auto;
}

int32 store(int32* p) {
    owns p[0..1];
    ensures result == 3 by auto;
}

int32 executed(int32 v) {
    ensures result == v;
} by {
    execute();
    simp();
}

int32 stepped(int32 v) {
    ensures result == v;
} by {
    step();
    step();
    step();
    step();
    simp();
}
```

```expect
pass
```
