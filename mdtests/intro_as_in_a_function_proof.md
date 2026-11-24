# Named intro in a function proof

`intro(name) { ... }` can open a universal in a C function proof: on
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
    step_until(function.exit);
    intro(below) {
        close();
    }
}

int32 keep_again(int32 x) {
    requires 0 <= x;
    ensures result == x;
} by {
    have forall (k: int32) { k < x implies k < x } by {
        intro(below) {
            intro() {
                close();
            }
        }
    }
}
```

```expect
pass
```
