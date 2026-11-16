# Plain and effectful do-while tests share continue routing

These retain the original cases beside `do_while_switch_continue.md`: a plain
test with a switch-enclosed continue, and an effectful test with a direct
continue. Each test executes at the loop's post-test destination.

```c filename=do_while_continue_shapes.c
int32 stop_now() {
    return 0;
}

int32 switch_continue_plain_condition() {
    int32 count = 0;
    int32 tail = 0;
    do {
        count++;
        switch (count) {
            case 1:
                continue;
            default:
                break;
        }
        tail++;
    } while (count < 3);
    return tail;
}

int32 call_condition_without_switch() {
    int32 count = 0;
    int32 tail = 0;
    do {
        count++;
        if (count == 1) {
            continue;
        }
        tail++;
    } while (stop_now());
    return tail;
}
```

```click
verifying "do_while_continue_shapes.c";

int32 stop_now() {
    ensures result == 0;
}

int32 switch_continue_plain_condition() {
    ensures result == 2;
}

int32 call_condition_without_switch() {
    ensures result == 0;
}
```

```expect
pass
```
