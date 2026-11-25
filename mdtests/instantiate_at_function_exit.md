# Instantiate available universals at function exit

The first instantiation adds a fact while the ownership claim is open. The
last instantiation closes the remaining proposition claim directly.

```c filename=instantiate_at_exit.c
int32 at_exit(int32* p, int32 n) { return n; }
```

```click
verifying "instantiate_at_exit.c";

function f(k: int32) -> int32 { k }
function g(k: int32) -> int32 { k }

int32 at_exit(int32* p, int32 n) {
    requires forall (k: int32) { f(k) == k };
    requires forall (k: int32) { g(k) == k };
    owns *p;
    ensures f(result) == result;
    ensures g(result) == result;
} by {
    step_until(function.exit);
    instantiate(forall (k: int32) { f(k) == k }, result);
    close();
    close();
    instantiate(forall (k: int32) { g(k) == k }, result);
}
```

```expect
pass
```
