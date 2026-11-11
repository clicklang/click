# Contract refinement eliminates an implication among the target's requirements

The explicit refinement theorem assumes the named contract's requirements
and proves the implementation's requirements. Here `flag == 1` and
`flag == 1 implies n == 7` establish `n == 7`. Applying that theorem supplies
the callback contract as an ordinary call prerequisite.

```c filename=implied_requirement.c
void use_seven(int32 flag, int32 n) {
}

void invoke_guarded(void (*callback)(int32, int32), int32 flag, int32 n) {
    callback(flag, n);
}

void guarded_caller(int32 flag, int32 n) {
    invoke_guarded(&use_seven, flag, n);
}
```

```click
verifying "implied_requirement.c";

contract void Guarded(int32 flag, int32 n) {
    requires flag == 1;
    requires flag == 1 implies n == 7;
    ensures 0 <= n;
}

void use_seven(int32 flag, int32 n) {
    requires n == 7;
    ensures 0 <= n;
}

void invoke_guarded(void (*callback)(int32, int32), int32 flag, int32 n) {
    requires Guarded(callback);
    requires flag == 1;
    requires n == 7;
    ensures 0 <= n;
}

theorem use_seven_is_guarded() {
    ensures Guarded(&use_seven) by {
        unfold(Guarded);
        solve();
    }
}

void guarded_caller(int32 flag, int32 n) {
    requires flag == 1;
    requires n == 7;
    ensures 0 <= n;
} by {
    apply(use_seven_is_guarded());
}
```

```expect
pass
```
