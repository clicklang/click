# intro as in a function proof

`intro() as name` works wherever `intro()` does in a C function's proof: on
a quantified postcondition after execution, and inside a `have` before it.

```c filename=intro_as_in_a_function_proof.c
int keep(int x) { return x; }
int keep_again(int x) { return x; }
```

```click
verifying "intro_as_in_a_function_proof.c";

int32 keep(int32 x) {
    requires 0 <= x;
    ensures forall (k: int32) { k < result implies k < x };
} by {
    execute();
    intro() as below;
    simp();
}

int32 keep_again(int32 x) {
    requires 0 <= x;
    ensures result == x;
} by {
    have forall (k: int32) { k < x implies k < x } by {
        intro() as below;
        intro();
        assumption();
    }
    execute();
    simp();
}
```

```expect
pass
```
