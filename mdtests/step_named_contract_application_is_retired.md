# The positional named-contract step is retired

A proof selects a named contract at a call by its name, `step(Exact)`, or by
its name and a map of its resource handles, `step(Read, { cell: first })`. The
retired application form, `step(Exact())` or `step(Exact(instance))`, is
refused with both replacements spelled out.

```c filename=main.c
int read_view(const int *(*f)(const int *), const int *p) { return f(p)[0]; }
```

```click
contract const int *Exact(const int *p) {
    views p[0..1];
    ensures result == p;
}
verifying "main.c";
int read_view(const int *(*f)(const int *), const int *p) {
    requires Exact(f);
    views p[0..1];
    ensures result == p[0];
} by { step(Exact()); execute(); simp(); }
```

```expect
fail: `step(Exact(...))` is retired; select a named contract with `step(Exact)`, or `step(Exact, { handle: instance })` when its body declares resource handles
```
