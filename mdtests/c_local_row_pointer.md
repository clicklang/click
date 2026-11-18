# A local pointer to an array row

```c filename=matrix.c
int second_row_first(void) {
    int matrix[2][3] = {{11, 12, 13}, {21, 22, 23}};
    int (*row)[3] = matrix;
    return row[1][0];
}
```

```click
verifying "matrix.c";
int32 second_row_first() { ensures result == 21; }
```

```expect
pass
```
