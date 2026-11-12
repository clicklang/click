# An explicit null fact supplies a theorem argument's object class

A C parameter carries its declared pointer type without promising an original
object class. An exact cited null equality permits any nominal object class;
checking this application does not search ownership anchors.

```c filename=null_class.c
struct node { int value; };
void keep(struct node *p) {}
```

```click
verifying "null_class.c";

theorem node_identity(p: struct node*) {
    ensures p == p by { normalize(); }
}

void keep(struct node *p) {
    requires p == 0;
    ensures p == 0;
} by {
    have p == p by {
        apply(node_identity(p)) using { p == 0; };
    }
    step_until(function.exit);
    assumption();
}
```

```expect
pass
```
