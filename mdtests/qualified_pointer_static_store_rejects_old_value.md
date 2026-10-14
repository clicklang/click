# A qualified function-static pointer postcondition observes its store

An input pointer equality cannot prove the same postcondition after storing a different pointer.

```c filename=static_slot.c
struct pair { int value; };
static int anchor;
void set_slot(int* p) { static int* slot = &anchor; slot = p; }
```
```click
verifying "static_slot.c" as unit;
void set_slot(int32* p) {
    owns unit::set_slot::slot;
    requires unit::set_slot::slot == &anchor;
    requires p != &anchor;
    ensures unit::set_slot::slot == &anchor;
} by { execute(); simp(); }
```
```expect
fail: ensures unit::set_slot::slot == &anchor
```
