# A C parameter keeps its binding under a cast
```c filename=seven.c
int32 seven(int32 result) { return 7; }
```
```click
verifying "seven.c";
int32 seven(int32 result) {
    requires 0 <= c(result) and c(result) <= 100;
    ensures ((int32)c(result)) == 7;
}
```
```expect
fail: unclosed goal
```
