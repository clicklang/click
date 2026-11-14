# Every untouched global reads its entry value

Function entry declares static storage without contents, so a read of a
global nothing has written is its load at `function.entry`, the same term as
`old(...)` of it and as a requirement about it. The first global a function
declares and every later one read alike: entry used to fill each global with
a placeholder read from a memory of its own, and only the first global's
placeholder happened to land on the entry memory, so `h` below spelled
`at(<state A>, h[0])` while `g` spelled `old(g[0])`.

A pointer global a resource clause is based at keeps its read, and a global
the function does not own reads the same beside an owned pointer
parameter's entry cells, as it did with the placeholder.

The negative twin is
[`an_untouched_later_global_spells_its_entry_read.md`](an_untouched_later_global_spells_its_entry_read.md).

```c filename=every_untouched_global_reads_its_entry_value.c
int32 g;
int32 h;
int32 *gp;

int32 read_g() {
    return g;
}

int32 read_h() {
    return h;
}

int32 read_both() {
    return g + h;
}

int32 read_through(int32 *p) {
    return *gp + *p + h;
}
```

```click
verifying "every_untouched_global_reads_its_entry_value.c";

int32 read_g() {
    ensures result == old(g);
}

int32 read_h() {
    requires h == 5;
    ensures result == 5;
    ensures result == old(h);
}

int32 read_both() {
    requires g == 1;
    requires h == 2;
    ensures result == 3;
}

int32 read_through(int32 *p) {
    owns gp[0..1];
    owns p[0..1];
    requires *gp == 1;
    requires *p == 2;
    requires h == 3;
    ensures result == 6;
}
```

```expect
pass
```
