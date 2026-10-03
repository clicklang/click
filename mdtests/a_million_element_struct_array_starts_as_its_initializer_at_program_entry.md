# a million-element struct array starts as its initializer at program entry

A program's entry knows the initial contents of its static storage. An array
of structs used to be zeroed at entry one field of one element at a time, so
a million-element pool cost millions of stores before `main` began. Each
scalar field is now one run of zeros stepping by the struct's size, and the
fields the initializer writes are stored over the runs.

Here `main` reads a written field, untouched `int32` and pointer fields, a
field of a nested struct, and a field it stores itself, in a file-scope pool
and a function-local `static` array of a million structs each.

```c filename=a_million_element_struct_array_starts_as_its_initializer_at_program_entry.c
struct point {
    int32 x;
    int32 y;
};

struct node {
    int32 key;
    struct node *next;
    struct point at;
};

struct node pool[1000000] = {[3] = {5}, [999999] = {6, 0, {7, 8}}};

int main(void) {
    static struct node spare[1000000] = {{1}};
    pool[500].key = 9;
    int32 empty = pool[4].next == 0;
    return pool[3].key + pool[4].key + empty + pool[500].key + pool[999999].at.y
        + pool[999998].at.x + spare[0].key + spare[999999].key;
}
```

```click
verifying "a_million_element_struct_array_starts_as_its_initializer_at_program_entry.c";

int main() {
    ensures result == 24;
} by {
    execute();
    simp();
}
```

```expect
pass
```
