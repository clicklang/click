# Pointer association keeps a shared symbolic base

Source-facing theorem pointers retain their own byte offset. The same checked
addition guard justifies regrouping the indices when that base is identical.

```c filename=simple.c
void keep(const uint8* p, int32 i) {}
```

```click
verifying "simple.c";

theorem bounded_pointer_association(base: const uint8*, index: int32) {
 requires 0 <= index;
 requires index <= 22200;
 ensures (base + index) + 4 == base + (index + 4) by {
  have defined(index + 4) by { simp() using { 0 <= index; index <= 22200; } }
  normalize() using { defined(index + 4); }
 }
}
```

```expect
pass
```
