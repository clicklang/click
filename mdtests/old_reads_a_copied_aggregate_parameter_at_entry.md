# Old reads the aggregate copy recorded at entry

```c filename=old_aggregate_entry.c
struct packet { int32* data; };
void touch(struct packet input) {}
```

```click
verifying "old_aggregate_entry.c";
void touch(struct packet input) {
    owns input.data[0..1];
    requires input.data[0] == 3;
} by {
    have input.data[0] == 3 by { assumption(); }
    have old(input.data[0]) == 3 by { assumption(); }
}
```

```expect
pass
```
