# A false `transport` in a `branch` arm is refused as on the main line

A branch arm uses the same ordinary transport search as the main proof.
The historical reflexive equality supplies no proof of the target value.

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
            transport(at(entry, a[m]) == at(entry, a[m]), at(entry, a[m]) == 5);
        }
        false => {
        }
    }
}
```

```expect
fail: `transport` found no checked proof from its source
```
