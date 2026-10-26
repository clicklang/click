# A read-only callee cannot initialize an uninitialized caller local

Passing a pointer grants the callee only the permissions stated by its
contract; it does not initialize the pointed-to storage. A callee that views
or owns `p[0..1]` may read it, so the call is refused while the caller's
`x` is unwritten; `initialize` writes before it reads and owns
`uninitialized(p[0..1])`.

```c filename=uninitialized_callee_resource_transfer.c
int32 same_twice(int32* p) {
    return p[0] == p[0];
}

void initialize(int32* p) {
    p[0] = 7;
}

int32 initialized_eq_callee() {
    int32 x;
    x = 7;
    return same_twice(&x);
}

int32 uninit_eq_callee() {
    int32 x;
    return same_twice(&x);
}

int32 same_owned(int32* p) {
    return p[0] == p[0];
}

int32 uninit_owned_callee() {
    int32* p = malloc(sizeof(int32));
    if (p == 0) {
        return 0;
    }
    int32 result = same_owned(p);
    free(p);
    return result;
}

int32 initialized_owned_callee() {
    int32* p = malloc(sizeof(int32));
    if (p == 0) {
        return 0;
    }
    initialize(p);
    int32 result = same_owned(p);
    free(p);
    return result;
}
```

```click
verifying "uninitialized_callee_resource_transfer.c";

int32 same_twice(int32* p) {
    views p[0..1];
    ensures result == 1;
}

int32 same_owned(int32* p) {
    owns p[0..1];
    ensures result == 1;
}

void initialize(int32* p) {
    owns uninitialized(p[0..1]);
    ensures p[0] == 7;
}

int32 initialized_eq_callee() {
    ensures result == 1;
}

int32 uninit_eq_callee() {
    ensures result == 1;
}

int32 uninit_owned_callee() {
    ensures result == 0 or result == 1;
}

int32 initialized_owned_callee() {
    ensures result == 0 or result == 1;
}
```

```expect
fail: holds its range as initialized, but the caller has not initialized every byte of it
```
