# A returned path uses its recorded result fact

`return a < b;` forks inside one expression, so each returned path has its
own `result`. After reaching function exit, `close()` closes the disjunction
from that path's recorded result fact without naming its value.

```c filename=exit_transport.c
int32 is_less(uint32 a, uint32 b) {
    return a < b;
}
```

```click
verifying "exit_transport.c";

int32 is_less(uint32 a, uint32 b) {
    ensures result == 0 or result == 1;
} by {
    step_until(function.exit);
    have result == 0 or result == 1 by {
        close();
    }
    close();
}
```

```expect
pass
```
