# A function head writes function-pointer typedef names

A parameter whose C type is a function-pointer typedef name of the verified
source is written with that name: `unary f` stands for `int (*f)(int)`, with
the alias's exact signature, and its named contract states what a call
through it returns. A `contract` head, which restates a signature rather
than a declaration, keeps its own C types.

```c filename=main.c
typedef int (*unary)(int);

int increment(int x) {
    return x + 1;
}

int apply(unary f, int x) {
    return f(x);
}
```

```click
verifying "main.c";

contract int Increments(int x) {
    requires x <= 1000;
    ensures result == x + 1;
}

int increment(int x) {
    requires x <= 1000;
    ensures result == x + 1;
} by {
    execute();
    simp();
}

int apply(unary f, int x) {
    requires Increments(f);
    requires x <= 1000;
    ensures result == x + 1;
} by {
    execute();
    simp();
}
```

```expect
pass
```
