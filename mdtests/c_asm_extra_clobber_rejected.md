# Inline assembly with a second clobber is rejected

Only the exact empty `memory` barrier is accepted.

```c filename=c_asm_extra_clobber_rejected.c
int32 run(int32 value) {
    __asm__ __volatile__("": : :"memory", "cc");
    return value;
}
```

```click
verifying "c_asm_extra_clobber_rejected.c";

```

```expect
fail:c_asm_extra_clobber_rejected.c:2: inline assembly is not supported, except the empty `__asm__ __volatile__("" : : : "memory")` barrier
```
