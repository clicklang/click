# Startup body completion still owes loop termination

Startup deliberately exposes no modular rule. Its completed partial body must
still discharge the program's return obligation.

```c filename=startup_loop.c
int main(void) {
    while (1) {}
    return 0;
}
```

```click
verifying "startup_loop.c";

int main() {
    ensures result == 0;
} by {
    loop {
        invariant true;
    }
}
```

```expect
fail: loop 0 declares no `decreases` measure
```
