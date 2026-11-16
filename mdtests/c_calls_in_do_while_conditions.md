# Calls in do-while conditions run after the body

The condition of a `do ... while` executes after the first body pass and after
an iteration reaches `continue`. The loop owns one shared checked post-test;
both body completion and `continue` leave the body scopes and transfer there.
The test is never copied into a continue's enclosing switch or branch.

```c filename=call_in_do_while_condition.c
int32 call_in_do_while_condition() {
    int32 count = 0;
    do {
        count++;
    } while (stop_now());
    do {
        count++;
        continue;
    } while (stop_now());
    return count;
}
```

```c filename=stop_now.c
int32 stop_now() {
    return 0;
}
```

```click
verifying "call_in_do_while_condition.c";
verifying "stop_now.c";

int32 call_in_do_while_condition() {
    ensures result == 2;
}

int32 stop_now() {
    ensures result == 0;
}
```

```expect
pass
```
