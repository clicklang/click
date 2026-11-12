# Owning an argument does not set a viewed private static

The helper's ownership/view partition separates `p->value` from the private
static. Its store therefore cannot establish that the value read from the
static is five. Passing the static itself as `p` is rejected by the call's
ownership/loan checks; the companion caller regression covers that refusal.

```c filename=library.c
struct counter { unsigned long value; };
static struct counter state = {7};
unsigned long set_then_read(struct counter *p) { p->value = 5; return state.value; }
unsigned long next(void) { return set_then_read(&state); }
```

```click
verifying "library.c" as library;

unsigned long set_then_read(struct counter *p) {
    owns p->value;
    views library::state.value;
    ensures result == 5u64;
}
```

```expect
fail: left side evaluated to old(state.value)
```
