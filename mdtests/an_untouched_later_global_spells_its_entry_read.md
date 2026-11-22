# An untouched later global spells its entry read

The negative twin of
[`every_untouched_global_reads_its_entry_value.md`](every_untouched_global_reads_its_entry_value.md).
`h` is the second global the function declares. Its current read still uses
the entry version, so the refused claim can name it directly as `h[0]`.

```c filename=an_untouched_later_global_spells_its_entry_read.c
int32 g;
int32 h;

int32 read_h() {
    return h;
}
```

```click
verifying "an_untouched_later_global_spells_its_entry_read.c";

int32 read_h() {
    ensures result == 3;
}
```

```expect
fail: left side evaluated to h[0], right side evaluated to 3
```
