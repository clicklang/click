# `normalize() using` refuses a narrow value the store did not write

The negative of
[`normalize_using_reads_a_narrow_stored_value.md`](normalize_using_reads_a_narrow_stored_value.md).
Under `j == 2` the store `t[j + 1] = 0` writes `t[3]`, not `t[2]`, so
`defined(t[2u64])` has no recorded store to read.

```c filename=narrow_store_elsewhere.c
int s(int j)
{
	unsigned char t[12];
	t[0] = 5;
	t[j+1] = 0;
	return t[0];
}
```

```click
verifying "narrow_store_elsewhere.c";

int32 s(int32 j) {
    requires 0 <= j and j <= 2;
    ensures result == 5;
} by {
    if j == 2 {
        step();
        step();
        step();
        have defined(t[2u64]) by { normalize() using { j == 2; }; }
        execute();
        simp();
    } else {
        if j == 1 { execute(); simp(); } else { execute(); simp(); }
    }
}
```

```expect
fail: did not normalize to true
```
