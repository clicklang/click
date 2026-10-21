# take after function exit says to move it

`take` moves an element at the execution frontier. After `execute()` reaches the exit there is none, and the refusal says so instead of reporting an unsupported proof shape.

```c filename=take_after_function_exit_says_to_move_it.c
void f(int *data, int *occupied, int capacity, int index) { }
```

```click
resource cells(data: int32*, occupied: int32*, capacity: int32) {
    owns occupied[0..capacity];
    forall (k: int32) where 0 <= k and k < capacity {
        if occupied[k] == 0 {
            owns data[k..k + 1];
        }
    }
}

verifying "take_after_function_exit_says_to_move_it.c";

void f(int32* data, int32* occupied, int32 capacity, int32 index) {
    owns cells(data, occupied, capacity);
    requires 0 <= index; requires index < capacity; requires occupied[index] == 0;
} by {
    unfold(cells(data, occupied, capacity));
    execute();
    take(data[index..index + 1]);
    give(data[index..index + 1]);
    fold(cells(data, occupied, capacity));
    simp();
}
```

```expect
fail: `take(data[index..(index + 1)])` must run before execution reaches function exit
```
