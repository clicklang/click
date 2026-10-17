# A cast cannot replace the type established by a fresh allocation

```c filename=heap.c
struct node { uint64 word; };
struct other { uint64 word; };
int32 accept(struct node* p) { return 7; }
int32 allocated() {
    struct other* p = malloc(sizeof(struct other));
    if (!p) return 7;
    int32 result = accept((struct node*)(void*)p);
    free(p);
    return result;
}
```

```click
verifying "heap.c";
int32 accept(struct node* p) { ensures result == 7; } by { execute(); simp(); }
int32 allocated() { ensures result == 7; } by { execute(); simp(); }
```

```expect
fail: passes an object of type `struct other`
```
