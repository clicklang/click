# Exceptional calls do not inherit normal memory guarantees

A normal postcondition must not leak onto the exceptional successor.

```c filename=exceptional_memory_permissions_are_returned.c
void update(int* value) { *value = 7; }
void relay(int* value) { update(value); }
```

```click
verifying "exceptional_memory_permissions_are_returned.c";
void update(int32* value) throws int32 {
    owns value[0];
    ensures value[0] == 7;
    exceptional ensures value[0] == 9;
}
void relay(int32* value) throws int32 {
    owns value[0];
    ensures value[0] == 7;
    exceptional ensures value[0] == 7;
}
```

```expect
fail: relay.exceptional_ensures_0
```
