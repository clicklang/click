# `auto` in a script closes every open goal

Written as a step of a script, `auto();` closes every goal still open in its
block, as the closer an omitted one stands for does. A closer written after it
has no goal left, so `normalize()` is refused.

```c filename=auto_in_a_script_closes_every_open_goal.c
int32 f(int32 n) {
    return n;
}
```

```click
verifying "auto_in_a_script_closes_every_open_goal.c";

int32 f(int32 n) {
    requires n == 1;
    ensures result == 1;
    ensures result == n;
} by {
    execute();
    auto();
    normalize();
}
```

```expect
fail: `normalize` has no goal to close
```
