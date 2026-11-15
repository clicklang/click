# An undeclared aggregate call must match the destination layout

```c filename=producer.c
struct single { int32 x; };
struct single make_pair() {
    struct single p = {3};
    return p;
}
```

```c filename=consumer.c
struct pair { int32 x; int32 y; };
int32 consume() {
    struct pair p = make_pair();
    return p.x;
}
```

```click
verifying "producer.c";
verifying "consumer.c";
struct single make_pair() { ensures result.x == 3; }
int32 consume() { ensures result == 3; } by { step_until(function.exit); }
```

```expect
fail: type mismatch
```
