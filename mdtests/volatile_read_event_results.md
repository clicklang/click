# Volatile observations retain typed results after their locals change

```c filename=volatile_results.c
void scalars(volatile int32 value) {
    int32 a = value;
    int32 b = value + value;
    value = 0;
}
int32 *pointer_result(int32 * volatile *cell) {
    int32 *saved = *cell;
    saved = 0;
    return saved;
}
int32 returned(volatile int32 value) { return value; }
```

```click
verifying "volatile_results.c";
void scalars(int32 value) {
    requires 0 <= value;
    requires value <= 10;
    ensures true;
} by {
    step_until(statement(2));
    have statement(0).result == statement(1).read_event(0).result by normalize();
    have statement(1).read_event(0).result == statement(1).read_event(1).result by normalize();
    step_until(function.exit);
    have statement(0).read_event(0).result == old(value) by normalize();
}
int32 *pointer_result(int32 **cell) {
    views *cell;
    ensures result == 0;
} by {
    step_until(statement(1));
    have statement(0).result == saved by normalize();
    step_until(function.exit);
    have statement(0).read_event(0).result == statement(0).result by normalize();
}
int32 returned(int32 value) { ensures result == value; } by {
    step_until(function.exit);
    have statement(0).result == result by normalize();
}
```

```expect
pass
```
