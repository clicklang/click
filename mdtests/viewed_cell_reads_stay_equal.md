# repeated reads of a viewed cell produce one value

This checks that `views` keeps the covered memory stable: two loads of `p[0]`
under a `views p[0..1]` clause read the same symbolic value.

```c filename=viewed_cell_reads_stay_equal.c
int32 peek(int32 p[]) {
    int32 a;
    int32 b;
    a = p[0];
    b = p[0];
    return a == b;
}
```

```click
verifying "viewed_cell_reads_stay_equal.c";

int32 peek(int32 p[]) {
    views p[0..1];
    ensures reads_agree: result == 1;
} by { execute(); simp(); }
```

```expect
pass
```
