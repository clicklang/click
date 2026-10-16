# A function head writes the source's typedef names

A function head restates its C declaration, and may write a typedef name of
the verified source for the type it stands for: a scalar alias such as `u32`
or `json_bool`, keeping a `long long` alias's rank, or a struct alias, named
or anonymous. The head still has exactly the declaration's types.

```c filename=main.c
typedef unsigned int u32;
typedef int json_bool;
typedef long long wide;
typedef const int fixed;
typedef struct node { int value; } node_t;
typedef struct { int x; int y; } point_t;

u32 twice(u32 n) {
    return n + n;
}

json_bool is_zero(wide *p) {
    return p[0] == 0;
}

int read_fixed(fixed *p) {
    return *p;
}

int node_value(node_t *node) {
    return node->value;
}

int point_x(const point_t *point) {
    return point->x;
}
```

```click
verifying "main.c";

u32 twice(u32 n) {
    requires n <= 1000u32;
    ensures result == n + n;
} by {
    execute();
    simp();
}

json_bool is_zero(wide *p) {
    views p[0];
    requires p[0] == 0;
    ensures result == 1;
} by {
    execute();
    simp();
}

int read_fixed(fixed *p) {
    views p[0];
    ensures result == p[0];
} by {
    execute();
    simp();
}

int node_value(node_t *node) {
    views node->value;
    ensures result == node->value;
} by {
    execute();
    simp();
}

int point_x(const point_t *point) {
    views point->x;
    ensures result == point->x;
} by {
    execute();
    simp();
}
```

```expect
pass
```
