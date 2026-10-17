# A return cast cannot manufacture a nominal object type

```c filename=case.c
struct node { int word; };
struct other { int word; };
```

```click
verifying "case.c";
function wrong(p: struct other*) -> struct node* { (struct node*)(void*)p }
theorem unrelated() { ensures 1 == 1 by normalize(); }
```

```expect
fail: function `wrong` return value requires original object class `struct node` or null
```
