# A declared pointer result does not excuse nonterminating recursion

```click
function forever(p: struct node*) -> struct node* { forever(p) }
theorem unrelated() { ensures 1 == 1 by normalize(); }
```

```expect
fail: recursive
```
