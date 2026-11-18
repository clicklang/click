# A row pointer does not authorize a read across an inner array boundary

```c filename=matrix.c
int read_past_row(void) {
    int matrix[2][3] = {{11, 12, 13}, {21, 22, 23}};
    int (*row)[3] = matrix;
    return row[0][3];
}
```

```click
verifying "matrix.c";
int32 read_past_row() { ensures result == result; }
```

```expect
fail: outside the subobject
```
