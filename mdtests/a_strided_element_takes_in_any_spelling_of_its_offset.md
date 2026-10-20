# A strided element takes in any spelling of its offset

The clause `owns data[2 * k..2 * k + 2];` names one element per `k`.
`take` and `give` accept that element with its offset in the clause's own
order `2 * index`, as `index * 2`, or as `index + index`: each has the affine
form `2 * index`.

```c filename=a_strided_element_takes_in_any_spelling_of_its_offset.c
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

verifying "a_strided_element_takes_in_any_spelling_of_its_offset.c";

void f(int32* data, int32* occupied, int32 capacity, int32 index) {
    owns pairs(data, occupied, capacity);
    requires 0 <= index; requires index < capacity; requires occupied[index] == 0;
} by {
    unfold(pairs(data, occupied, capacity));
    take(data[2 * index..2 * index + 2]);
    give(data[index + index..index + index + 2]);
    fold(pairs(data, occupied, capacity));
    execute();
    simp();
}
```

```expect
pass
```
