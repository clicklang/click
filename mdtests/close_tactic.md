# Close checks the current goal before searching

```c filename=identity.c
int identity(int x) { return x; }
```

```click
verifying "identity.c";

theorem closes_from_a_fact(x: int32) {
    requires x == 0;
    ensures x == 0 by close();
}

theorem closes_by_search(x: int32) {
    ensures x == 0 implies x == 0 by close();
}

int32 identity(int32 x) {
    ensures result == x;
} by {
    step();
    close();
}
```

```expect
pass
```
