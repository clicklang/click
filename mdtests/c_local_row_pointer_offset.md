# Advancing a row pointer scales by the row width

```c filename=matrix.c
int select_rows(void) {
    int matrix[2][3] = {{11, 12, 13}, {21, 22, 23}};
    int (*row)[3] = matrix;
    int (*next)[3] = row + 1;
    next[0][0] = 31;
    ++next;
    return next[-2][1] + matrix[1][0];
}
```

```click
verifying "matrix.c";
int32 select_rows() { ensures result == 43; }
```

```expect
pass
```
