# The barrier must be written `volatile`

Only the exact empty `memory` barrier is accepted.

```c filename=c_asm_non_volatile_rejected.c
int32 run(int32 value) {
    __asm__("": : :"memory");
    return value;
}
```

```click
verifying "c_asm_non_volatile_rejected.c";

```

```expect
fail:c_asm_non_volatile_rejected.c:2: inline assembly is not supported, except the empty `__asm__ __volatile__("" : : : "memory")` barrier
```
