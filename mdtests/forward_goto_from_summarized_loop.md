# A checked loop returns a jump to its named cleanup label

```c filename=summarized.c
int32 scan(int32 n) {
    while (1) {
        if (n == 0) goto done;
        n--;
    }
    n = 99;
done:
    return n;
}
```

```click
verifying "summarized.c";

int32 scan(int32 n) {
    requires n >= 0;
    ensures result == 0;
} by {
    loop {
        invariant n >= 0;
        decreases n;
    }
}
```

```expect
pass
```
