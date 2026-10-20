# intro opens a written negation and a disequality

`not (n == 1)` lowers to the comparison `n != 1`, and `not (x >= y)` to
`x < y`. `intro()` opens a goal written as `not P`, and a disequality, which
is the negation of an equality: `P` becomes a fact and the goal is `false`.

```c filename=intro_opens_a_written_negation_and_a_disequality.c
void unused(void) {}
```

```click
verifying "intro_opens_a_written_negation_and_a_disequality.c";

theorem written_negation(n: int32) {
    requires n == 0;
    ensures not (n == 1) by {
        intro();
        arithmetic() using { n == 0; n == 1; };
    }
}

theorem disequality(a: Integer, b: Integer) {
    requires a < b;
    ensures a != b by {
        intro();
        arithmetic() using { a < b; a == b; };
    }
}

theorem written_order_negation(x: int32, y: int32) {
    requires x < y;
    ensures not (x >= y) by {
        intro();
        contradiction(x < y);
    }
}
```

```expect
pass
```
