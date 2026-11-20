# A declared resource named view keeps the ordinary produces syntax

```c filename=named_view.c
void make_view(int n);
void use(int n) { make_view(n); }
```

```click
verifying "named_view.c";

extern void make_view(int32 n) {
    produces view(n);
}

void use(int32 n) {
    produces view(n);
}

resource view(n: int32) {
    fact n == n;
}
```

```expect
pass
```
