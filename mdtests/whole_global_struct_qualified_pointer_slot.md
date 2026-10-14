# A qualified struct pointer global still names only its pointer slot

```c filename=pointer_slot.c
struct pair { uint64 left; uint64 right; };
static struct pair* slot = 0;
void clear_slot() { slot = 0; }
```
```click
verifying "pointer_slot.c" as unit;
void clear_slot() {
    owns unit::slot;
} by { execute(); simp(); }
```
```expect
pass
```
