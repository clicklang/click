# definedness is a step requirement

`x + 1` is defined when `x == 5 or x == 7`, but the kernel's fast check does
not split the disjunction. Definedness is one of the statement's
requirements, like a callee's precondition: the implicit `auto` proves it
under a bare `step()`, and a written `step() by { ... }` proves it
explicitly. A shift's requirement is its count's whole range.

```c filename=definedness_is_a_step_requirement.c
int next(int x) { return x + 1; }
unsigned shifted(unsigned x, int s) { return x << s; }
```

```click
verifying "definedness_is_a_step_requirement.c";

int32 next(int32 x) {
    requires x == 5 or x == 7;
    ensures result == x + 1;
} by {
    step() by {
        cases {
            x == 5 => { simp(); }
            x == 7 => { simp(); }
        }
    }
    simp();
}

uint32 shifted(uint32 x, int32 s) {
    requires s == 1 or s == 2;
    ensures result == result;
} by {
    step();
    simp();
}
```

```expect
pass
```
