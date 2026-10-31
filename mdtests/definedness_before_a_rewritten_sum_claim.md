# Establish a rewritten machine sum's domain before observing it

A `have` claim lowers before its proof body runs. Transfer the machine sum's
definedness through the selected field equality first; then its observed bound
can lower and the same equality rewrites it to the available bound.

```c filename=sum.c
void check_sum(int *start, int s, int index, int end) { }
```

```click
verifying "sum.c";

void check_sum(int32* start, int32 s, int32 index, int32 end) {
    views *start;
    requires *start == s;
    requires defined(s + index) and to_integer(s + index) < to_integer(end);
    ensures true;
} by {
    have to_integer(s + index + 1) <= to_integer(end);
    have defined(s + index + 1);
    have defined(*start + index + 1) by {
        rewrite(*start == s);
        assumption();
    }
    have to_integer(*start + index + 1) <= to_integer(end) by {
        rewrite(*start == s);
        assumption();
    }
}
```

```expect
pass
```
