# An observed pointer is not made null by naming its event

```c filename=volatile_false.c
int32 *f(int32 * volatile *cell) {
    int32 *saved = *cell;
    saved = 0;
    return saved;
}
```
```click
verifying "volatile_false.c";
int32 *f(int32 **cell) { views *cell; ensures result == 0; } by {
    step_until(function.exit);
    have statement(0).read_event(0).result == 0;
}
```
```expect
fail: could not establish `statement(0).read_event(0).result == 0`
```
