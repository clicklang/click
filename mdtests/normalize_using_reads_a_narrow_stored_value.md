# A checked address equality identifies a narrow stored read

Linux `string_get_size` ends its fraction by writing `tmp[j + 1] = '\0'`.
With `j == 2`, the proof calculates the address equality
`&t[3u64] == &t[j + 1]`. Rewriting that address in both goals exposes the
store's recorded value and the fact that all bytes of the read were written.

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
        have &t[3u64] == &t[j + 1] by { rewrite(j, 2); close(); }
        have t[3u64] == 0u8 by {
            rewrite(&t[3u64], &t[j + 1]);
            close();
        }
        have defined(t[3u64]) by {
            rewrite(&t[3u64], &t[j + 1]);
            close();
        }
        step_until(function.exit);
        close();
    } else {
        if j == 1 { step_until(function.exit); close(); } else { step_until(function.exit); close(); }
    }
}
```

```expect
pass
```
