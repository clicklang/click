# Restricted simplification after execution

A selected-premise closer at function exit must use the checked outcome proof
and retain the preceding `have`, rather than declining the whole script.

```c filename=post_simp.c
int32 one(void) { return 1; }
```
```click
verifying "post_simp.c";
int32 one() { ensures result == 1; } by {
 execute();
 have result == 1;
 simp() using { result == 1; }
}
```
```expect
pass
```
