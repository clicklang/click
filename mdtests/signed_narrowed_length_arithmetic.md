# Signed observations of a narrowed length have printable arithmetic certificates

The low word is an opaque signed value. Its explicit bounds support arithmetic;
none of these facts imply a bound on the original native-width length. Snapshot
operands retain their selectors after the source local changes.

```c filename=signed_narrowed_length_arithmetic.c
int32 distance(uint64 n, int32 remaining) {
    remaining = remaining - 1;
    return remaining;
}
```

```click
verifying "signed_narrowed_length_arithmetic.c";
int32 distance(uint64 n, int32 remaining) {
    requires 0 < remaining;
    requires remaining <= (int32)(uint32)n;
    requires 0 <= (int32)(uint32)n;
    requires 1000 >= (int32)(uint32)n;
    ensures ((int32)(uint32)n - result - 1) < (int32)(uint32)n;
} by {
    step();
    have ((int32)(uint32)n - remaining - 1) < (int32)(uint32)n by {
        arithmetic() using {
            at(statement(0).entry, 0 < remaining);
            at(statement(0).entry, remaining <= (int32)(uint32)n);
            0 <= (int32)(uint32)n;
            1000 >= (int32)(uint32)n;
        }
    }
    have 1000 >= ((int32)(uint32)n - remaining - 1) by {
        arithmetic() using {
            at(statement(0).entry, 0 < remaining);
            at(statement(0).entry, remaining <= (int32)(uint32)n);
            0 <= (int32)(uint32)n; 1000 >= (int32)(uint32)n;
        }
    }
    execute(); simp();
}
```

```expect
pass
```
