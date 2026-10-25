# Restricted simplification after execution

A selected-premise closer at function exit must use the checked outcome proof
and retain the preceding `have`, rather than declining the whole script.

```c filename=post_simp.c
int32 one(void) { return 1; }
```
```click
verifying "post_simp.c";
int32 one() { ensures result == 1; } by {
 step_until(function.exit);
 have result == 1;
 solve() using { result == 1; };
}
```
```expect
pass
```
