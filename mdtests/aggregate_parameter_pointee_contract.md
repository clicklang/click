# Logical parameter fields preserve values without preserving C storage

```c filename=aggregate_parameter_pointee_contract.c
struct inner { int32 value; };
struct packet { struct inner inner; int32 items[2]; int32* data; };

int32 touch(struct packet input) { input.data[0] = 7; return input.data[0]; }
```

```click
verifying "aggregate_parameter_pointee_contract.c";
int32 touch(struct packet input) {
    consumes input.data[0..1];
    requires input.data[0] == 3;
    produces input.data[0..1];
    ensures result == 7;
    ensures input.data[0] == 7;
    ensures old(input.data[0]) == 3;
} by {
    mark copied_entry;
    have old(input.data[0]) == 3 by { assumption(); }
    have at(copied_entry, input.data) == old(input.data);
    have at(copied_entry, input.data[0]) == old(input.data[0]) by {
        rewrite(at(copied_entry, input.data) == old(input.data));
        normalize();
    }
    have at(copied_entry, input.data[0]) == 3;
    step_until(function.exit);
    have old(input.data) == at(copied_entry, input.data);
    have old(input.data[0]) == at(copied_entry, input.data[0]) by {
        rewrite(old(input.data) == at(copied_entry, input.data));
        normalize();
    }
    have old(input.data[0]) == 3;
}

```

```expect
pass
```
