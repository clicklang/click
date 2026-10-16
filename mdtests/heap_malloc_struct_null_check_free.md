# Allocate a struct, check for null, store, and free it

A declaration initialized by `malloc(sizeof(struct item))` is refined by a
null check; the successful path stores the field before freeing the object.

```c filename=heap_malloc_struct_null_check_free.c
struct item {
    int32 value;
};

int32 make_and_free() {
    struct item *item = malloc(sizeof(struct item));
    if (item == 0) {
        return 0;
    }
    item->value = 1;
    free(item);
    return 1;
}
```

```click
verifying "heap_malloc_struct_null_check_free.c";

int32 make_and_free() {
    ensures result >= 0 by auto();
}
```

```expect
pass
```
