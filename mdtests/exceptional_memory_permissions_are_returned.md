# Exceptional calls return borrowed memory permissions

The callee's exceptional memory can differ from its normal result. Both
outcomes return exactly the memory authority the caller lent.

```c filename=exceptional_memory_permissions_are_returned.c
void update(int* value, const int* observed) { *value = 7; }
void relay(int* value, const int* observed) { update(value, observed); }
```

```click
verifying "exceptional_memory_permissions_are_returned.c";
void update(int32* value, const int32* observed) throws int32 {
    owns value[0];
    views observed[0];
    ensures value[0] == 7;
    ensures observed[0] == old(observed[0]);
    exceptional ensures value[0] == 9;
    exceptional ensures observed[0] == old(observed[0]);
}
void relay(int32* value, const int32* observed) throws int32 {
    owns value[0];
    views observed[0];
    ensures value[0] == 7;
    ensures observed[0] == old(observed[0]);
    exceptional ensures value[0] == 9;
    exceptional ensures observed[0] == old(observed[0]);
}
```

```expect
pass
```
