# A C address-only cast return needs no positive object-type premise

```c filename=returns.c
struct model_node { uint64 word; };
struct model_node* wrong(void* p) { return (struct model_node*)p; }
```

```click
verifying "returns.c";
struct model_node* wrong(void* p) { ensures address(result) == address(p); } by {
    execute(); normalize();
}
```

```expect
pass
```
