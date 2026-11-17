# A switch continue reaches the shared do-while test

The continue leaves the switch and body before evaluating the loop's shared
post-test. A false test exits the loop, so `tail` stays zero.

```c filename=do_while_switch_continue_rejected.c
int32 stop_now() {
    return 0;
}

int32 do_while_switch_continue_rejected() {
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
    } while (stop_now());
    return tail;
}
```

```click
verifying "do_while_switch_continue_rejected.c";

int32 stop_now() {
    ensures result == 0;
}

int32 do_while_switch_continue_rejected() {
    ensures result == 0;
}
```

```expect
pass
```
