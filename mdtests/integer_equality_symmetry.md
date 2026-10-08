# Integer equality citations are independent of orientation

```c filename=integer_equality_symmetry.c
void unchanged(int32 x) {}
```

```click
verifying "integer_equality_symmetry.c";

theorem equal_arguments(a: Integer, b: Integer) {
    requires a == b;
    ensures a == b by assumption();
}

theorem reverse_requirement(a: Integer, b: Integer) {
    requires b == a;
    ensures a == b by {
        apply(equal_arguments(a, b)) using { b == a; }
    }
}

theorem reverse_citation(a: Integer, b: Integer) {
    requires b == a;
    ensures a == b by {
        apply(equal_arguments(a, b)) using { a == b; }
    }
}

theorem reverse_transport(a: Integer, b: Integer) {
    requires b == a;
    ensures a == b by {
        transport(b == a, a == b) using { b == a; }
    }
}

void unchanged(int32 x) {
    requires to_integer(x) == 10;
    ensures 10 == old(to_integer(x));
} by {
    execute();
    apply(equal_arguments(10, old(to_integer(x)))) using { old(to_integer(x)) == 10; }
    simp();
}
```

```expect
pass
```
