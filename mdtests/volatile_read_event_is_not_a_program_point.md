# An observation result is not a stepping boundary

```c filename=volatile_point.c
int32 f(volatile int32 value) { return value; }
```
```click
verifying "volatile_point.c";
int32 f(int32 value) { ensures result == value; } by {
    step_until(statement(0).read_event(0));
}
```
```expect
fail: selects a volatile observation's `.result`, not a statement boundary
```
