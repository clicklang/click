# Current memory through an entry-state pointer

The pointer's snapshot and the memory snapshot are independent. The write
changes current memory, and assigning the parameter does not change `old(p)`.

```c filename=current_load_through_old_pointer.c
void write(int32* p, int32* q) { *p = 7; p = q; }
```

```click
verifying "current_load_through_old_pointer.c";

void write(int32* p, int32* q) {
    owns p[0..1];
    ensures load_int32(old(p)) == 7;
} by { execute(); simp(); }
```

```expect
pass
```
