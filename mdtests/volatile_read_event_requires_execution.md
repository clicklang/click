# A volatile read event cannot be named before execution

```c filename=volatile_future.c
int32 f(volatile int32 value) { return value; }
```
```click
verifying "volatile_future.c";
int32 f(int32 value) { ensures result == value; } by {
    have statement(0).read_event(0).result == value;
}
```
```expect
fail: no recorded volatile read result
```
