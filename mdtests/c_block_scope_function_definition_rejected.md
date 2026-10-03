# A block-scope function declaration must be a prototype

C has no nested function definitions; the GNU extension is not modeled.

```c filename=c_block_scope_function_definition_rejected.c
int32 run(int32 value) {
    extern void helper(void) { }
    return value;
}
```

```click
verifying "c_block_scope_function_definition_rejected.c";

```

```expect
fail:c_block_scope_function_definition_rejected.c:2: block-scope declaration of `helper` must be a body-less function prototype
```
