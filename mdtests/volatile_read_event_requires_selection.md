# Multiple observations need an explicit event index

```c filename=volatile_pair.c
int32 f(volatile int32 value) { return value + value; }
```
```click
verifying "volatile_pair.c";
int32 f(int32 value) {
    requires 0 <= value;
    requires value <= 10;
    ensures true;
} by {
    step_until(function.exit);
    have statement(0).result == value;
}
```
```expect
fail: multiple volatile reads: select `.read_event(i).result`
```
