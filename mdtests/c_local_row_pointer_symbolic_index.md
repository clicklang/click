# A local row pointer accepts a symbolic integer index

```c filename=matrix.c
int read_row(int which) {
    int matrix[2][3] = {{11, 12, 13}, {21, 22, 23}};
    int (*row)[3] = matrix;
    return row[which][0];
}
```

```click
verifying "matrix.c";
int32 read_row(int32 which) {
    requires 0 <= which and which < 2;
    ensures which == 0 implies result == 11;
    ensures which == 1 implies result == 21;
}
```

```expect
pass
```
