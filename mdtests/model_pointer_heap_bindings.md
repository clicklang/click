# Fresh allocations retain their first struct type across checked calls

```c filename=heap.c
struct node { uint64 word; };
int32 accept(struct node* p) { return 7; }
int32 allocated() {
    struct node* p = malloc(sizeof(struct node));
    if (!p) return 7;
    p->word = 3;
    int32 result = accept(p);
    free(p);
    return result;
}
int32 zeroed() {
    struct node* p = calloc(1, sizeof(struct node));
    if (!p) return 7;
    int32 result = accept(p);
    free(p);
    return result;
}
```

```click
verifying "heap.c";
int32 accept(struct node* p) { ensures result == 7; } by { execute(); simp(); }
int32 allocated() { ensures result == 7; } by { execute(); simp(); }
int32 zeroed() { ensures result == 7; } by { execute(); simp(); }
```

```expect
pass
```
