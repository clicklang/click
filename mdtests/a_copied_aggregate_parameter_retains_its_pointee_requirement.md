# A copied aggregate parameter retains its pointee requirement

```c filename=aggregate_entry_read.c
struct packet { int32* data; };
void touch(struct packet input) {}
```

```click
verifying "aggregate_entry_read.c";
void touch(struct packet input) {
    owns input.data[0..1];
    requires input.data[0] == 3;
} by {
    have input.data[0] == 3 by { assumption(); }
}
```

```expect
pass
```
