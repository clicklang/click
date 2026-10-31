# An unknown invariant name is a type error before proof execution

```c filename=lp.c
int lp(int n) { int i = 0; while (i < n) { i = i + 1; } return i; }
```

```click
verifying "lp.c";
int32 lp(int32 n) {
 requires n >= 0;
 ensures result == n;
} by {
 step_until(loop(0));
 loop {
  decreases n - i;
  invariant bogus <= n;
  invariant 0 <= i and i <= n;
 }
}
```

```expect
fail: unknown name `bogus` in loop invariant clause
```
