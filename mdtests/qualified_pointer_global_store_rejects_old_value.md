# A qualified pointer postcondition must observe the store

The input null fact cannot justify retaining null after storing a non-null pointer.
```c filename=pointer_slot.c
struct pair { unsigned long left; unsigned long right; };
static struct pair* slot = 0;
void set_slot(struct pair* p) { slot = p; }
```
```click
verifying "pointer_slot.c" as unit;
void set_slot(struct pair* p) {
    owns unit::slot;
    requires unit::slot == 0;
    requires p != 0;
    ensures unit::slot == 0;
} by { execute(); simp(); }
```
```expect
fail: ensures unit::slot == 0
```
