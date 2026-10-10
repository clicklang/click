# Read-only automatic scalar initialization

A read-only local has initialized storage and retains an address for alias reads.

```c filename=readonly.c
int32 probe() {
    const int32 value = 7;
    const int32* alias = &value;
    return *alias;
}
```

```click
verifying "readonly.c";

int32 probe() {
    ensures result == 7;
} by {
    execute();
    simp();
}
```

```expect
pass
```
