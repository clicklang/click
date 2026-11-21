# A region footprint is a resource-valued theorem argument

```c filename=argument.c
void write_cell(int *p, int *q) { *p = 7; }
```

```click
import click::separation;
verifying "argument.c";
void write_cell(int *p, int *q) {
    owns *p;
    views *q;
    requires separate(memory(*p), memory(*q));
} by {
    step();
    have contains(statement(0).footprint, statement(0).footprint) by {
        apply(click::separation::contains_refl(statement(0).footprint)) using { };
    }
    have contains(memory(*q), memory(*q)) by { apply(click::separation::contains_refl(memory(*q))) using {}; }
    have separate(statement(0).footprint, memory(*q)) by {
        solve() using { separate(memory(*p), memory(*q)); };
    }
    have separate(statement(0).footprint, memory(*q)) by {
        apply(separation::separate_restrict(statement(0).footprint, memory(*q),
            statement(0).footprint, memory(*q))) using {
            separate(statement(0).footprint, memory(*q));
            contains(statement(0).footprint, statement(0).footprint);
            contains(memory(*q), memory(*q));
        };
    }
}
```

```expect
pass
```
