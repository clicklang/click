# Separately proved claims certify in authority mode

Each claim has its own proof, so each proof builds its own entry state with
a fresh, empty creation ledger. Certification identifies ledgers that record
nothing, so every claim's completion matches the certified entry state.

```c filename=set_cell.c
int32 set_cell(int32 p[], int32 value) {
    p[0] = value;
    return value;
}
```

```c filename=set_then_read.c
int32 set_then_read(int32 p[], int32 value) {
    int32 ignored;
    ignored = set_cell(p, value);
    return p[0];
}
```

```click
verifying "set_cell.c";
verifying "set_then_read.c";

int32 set_cell(int32 p[], int32 value) {
    owns p[0..1] by auto;
    ensures p[0] == value by auto;
    ensures result == value by auto;
}

int32 set_then_read(int32 p[], int32 value) {
    owns p[0..1] by {
        step();
        step();
        step();
    }
    ensures result == value by {
        step();
        step();
        step();
        simp();
    }
}
```

```expect
pass
```
