# explicit scripts execute C before simp, and simp can restrict its premises

This checks the two script shapes from the proof-scripts concept page: a
whole-function proof that runs `execute()` before `simp()`, and a `simp()`
whose search is restricted to the facts listed in `using`.

```c filename=identity_value.c
int32 identity_value(int32 x) {
    return x;
}
```

```c filename=checked_index.c
int32 checked_index(int32 i, int32 n) {
    return i;
}
```

```click
verifying "identity_value.c";
verifying "checked_index.c";

int32 identity_value(int32 x) {
    ensures result == x by {
        execute();
        simp();
    }
}

int32 checked_index(int32 i, int32 n) {
    requires i >= 0;
    requires i < n;
    ensures in_range: 0 <= i and i < n and result == i by {
        execute();
        simp() using {
            i >= 0;
            i < n;
        }
    }
}
```

```expect
pass
```
