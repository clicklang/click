# Function-pointer store equations retain the latest callback target

```c filename=callbacks.c
struct callbacks { int32 (*call)(void); };
int32 first() { return 1; }
int32 second() { return 2; }
int32 call_latest(struct callbacks *p) {
    p->call = first;
    p->call = second;
    return p->call();
}
```

```click
verifying "callbacks.c";
int32 first() { ensures result == 1; }
int32 second() { ensures result == 2; }
int32 call_latest(struct callbacks* p) {
    owns p->call;
    ensures result == 2;
}
```

```expect
pass
```
