# An indexed slot uses the declared stride

An indexed unfold exposes the two-cell element from the clause. Its matching
fold restores it. Each tactic supplies only the logical index.

```c filename=indexed_strided_slot_uses_the_declared_stride.c
void f(int *data, int *occupied, int capacity, int index) { }
```

```click
resource pairs(data: int32*, occupied: int32*, capacity: int32) {
    owns occupied[0..capacity];
    forall (k: int32) where 0 <= k and k < capacity {
        if occupied[k] == 0 {
            owns data[2 * k..2 * k + 2];
        }
    }
}

verifying "indexed_strided_slot_uses_the_declared_stride.c";

void f(int32* data, int32* occupied, int32 capacity, int32 index) {
    owns pairs(data, occupied, capacity);
    requires 0 <= index; requires index < capacity; requires occupied[index] == 0;
} by {
    unfold(pairs(data, occupied, capacity));
    unfold(pairs(data, occupied, capacity)[index]);
    fold(pairs(data, occupied, capacity)[index]);
    fold(pairs(data, occupied, capacity));
}
```

```expect
pass
```
