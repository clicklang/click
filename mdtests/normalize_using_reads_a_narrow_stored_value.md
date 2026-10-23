# `normalize() using` reads a narrow stored value

Linux `string_get_size` ends its fraction with `tmp[j+1] = '\0'`. With `j`
known, the byte it wrote is at a constant offset, but the store's address is
spelled with `j`, so no fact about `tmp[3]` holds by its term alone.

`normalize() using { j == 2; }` justifies a read's recorded stored value from
the cited conditions: the bounded memory-history walk reaches the store
`t[j + 1] = 0` and, reading `j == 2`, finds it writes the read's byte. That
gives the read's value, `t[3u64] == 0u8`, and that it reads written bytes,
`defined(t[3u64])`, for reads of every width. A wrong value, a byte the store
did not write, or a premise that does not place the store are refused.

```c filename=narrow_store.c
int s(int j)
{
	unsigned char t[12];
	t[0] = 5;
	t[j+1] = 0;
	return t[0];
}
```

```click
verifying "narrow_store.c";

int32 s(int32 j) {
    requires 0 <= j and j <= 2;
    ensures result == 5;
} by {
    if j == 2 {
        step();
        step();
        step();
        have t[3u64] == 0u8 by { normalize() using { j == 2; }; }
        have defined(t[3u64]) by { normalize() using { j == 2; }; }
        execute();
        simp();
    } else {
        if j == 1 { execute(); simp(); } else { execute(); simp(); }
    }
}
```

```expect
pass
```
