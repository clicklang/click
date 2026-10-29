# Historical pointee values survive both free and parameter exit

```c filename=aggregate_parameter_old_pointee.c
struct packet { int32* data; };
void dispose(struct packet input) { free(input.data); }
```

```click
verifying "aggregate_parameter_old_pointee.c";
resource cell(p: int32*) {
    owns allocation(p, 4);
    owns p[0..1];
}
void dispose(struct packet input) {
    consumes cell(input.data);
    requires input.data[0] == 7;
    ensures old(input.data[0]) == 7;
} by {
    unfold(cell(input.data));
    mark copied_entry;
    have old(input.data[0]) == 7 by { assumption(); }
    have at(copied_entry, input.data) == old(input.data);
    have at(copied_entry, input.data[0]) == old(input.data[0]) by {
        rewrite(at(copied_entry, input.data) == old(input.data));
        normalize();
    }
    have at(copied_entry, input.data[0]) == 7;
    step_until(function.exit);
    have old(input.data) == at(copied_entry, input.data);
    have old(input.data[0]) == at(copied_entry, input.data[0]) by {
        rewrite(old(input.data) == at(copied_entry, input.data));
        normalize();
    }
    have old(input.data[0]) == 7;
    solve();
}
```

```expect
pass
```
