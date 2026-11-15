# numeric recursion compares the call with the immutable entry measure

Reassigning the C parameter does not invalidate its entry measure. The
ordinary call obligation must prove descent from that entry value.

```c filename=c_decreases_parameter_reassignment_descends.c
int32 countdown(int32 n) {
    if (n > 0) {
        n = n - 1;
        return countdown(n);
    }
    return 0;
}
```

```click
verifying "c_decreases_parameter_reassignment_descends.c";

int32 countdown(int32 n) {
    decreases n;
    requires n >= 0;
    ensures result == 0;
}
```

```expect
pass
```
