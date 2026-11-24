# Word store equations survive aliases and overwrites

Store equations establish the value at their own program point. An overwrite
must not change the earlier equation or make it true at the later point.

```c filename=put.c
void put(int32* p, int32* q) {
    *p = 7;
    *p = 9;
}
```

```click
verifying "put.c";
void put(int32* p, int32* q) {
    requires p == q;
    owns p[0..1];
    ensures *p == 9;
} by {
    step();
    mark first;
    have *p == 7 by { close(); }
    have *q == 7 by { rewrite(q, p); close(); }
    step();
    have *p == 9 by { close(); }
    have at(first, *p) == 7 by { close(); }
}
```

```expect
pass
```
