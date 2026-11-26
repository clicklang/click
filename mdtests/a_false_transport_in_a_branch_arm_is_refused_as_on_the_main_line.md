# A false historical claim fails in a branch arm

Preserving the array element does not establish what value it originally held.

```c filename=a_false_transport_in_a_branch_arm_is_refused_as_on_the_main_line.c
void mark_one(int32 a[], int32 n, int32 i, int32 m, int32 c) {
    if (c) {
        a[i] = 1;
    }
}
```

```click
verifying "a_false_transport_in_a_branch_arm_is_refused_as_on_the_main_line.c";

void mark_one(int32 a[], int32 n, int32 i, int32 m, int32 c) {
    requires 0 <= i;
    requires i < n;
    requires 0 <= m;
    requires m < n;
    requires m != i;
    requires n <= 1073741823;
    owns a[0..n];
    ensures a[m] == old(a[m]);
} by {
    mark entry;
    branch {
        true => {
            step();
            have at(entry, a[m]) == 5 by { close(); }
        }
        false => {
        }
    }
}
```

```expect
fail: could not establish `at(entry, a[m]) == 5`
```
