# The empty `memory` barrier does nothing in the sequential semantics

The Linux `barrier()` macro is `__asm__ __volatile__("" : : : "memory")`: an empty template, no operands, and a `memory` clobber. It emits no instruction. This is a claim about sequential execution only; what the barrier tells the compiler about reordering, and so its meaning for concurrent readers, is outside it.

```c filename=c_asm_memory_barrier.c
int32 run(int *cell, int32 value) {
    *cell = value;
    __asm__ __volatile__("": : :"memory");
    asm volatile("" ::: "memory");
    return *cell;
}
```

```click
verifying "c_asm_memory_barrier.c";

int32 run(int32* cell, int32 value) {
    owns cell[0..1];
    ensures result == value by auto;
}
```

```expect
pass
```
