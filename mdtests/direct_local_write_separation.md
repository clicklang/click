# A direct assignment requires separation from a live view

The C body takes the local's address. The direct write proves separation of
that same slot from the viewed input.

```c filename=direct_local_write_separation.c
int set_local(const int *viewed) {
    int local = 0;
    int *address = &local;
    local = 7;
    return *address;
}
```

```click
verifying "direct_local_write_separation.c";

int set_local(const int *viewed) {
    views viewed[0..1];
    ensures result == 7;
} by {
    step();
    step();
    step();
    step();
    have separate(memory((&local)[0..1]), memory(viewed[0..1])) by { solve(); }
    step() by { known(); }
}
```

```expect
pass
```
