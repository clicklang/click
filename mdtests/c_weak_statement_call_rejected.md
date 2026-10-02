# A discarded call to a weak function is rejected

A weak function may be absent at link time, so a call needs an availability
model in statement position as well as in value position. An `extern`
contract does not supply that model.

```c filename=c_weak_statement_call_rejected.c
__attribute__((weak)) int optional(int code);

int32 run(int32 value) {
    optional(value);
    return value;
}
```

```click
verifying "c_weak_statement_call_rejected.c";

extern int32 optional(int32 code) {
    ensures result == code;
}

int32 run(int32 value) {
    ensures result == value by auto;
}
```

```expect
fail:c_weak_statement_call_rejected.c:4: weak function `optional` may be absent; calls need an availability model
```
