# A view of file-scope storage does not authorize a store into it

A `views` clause over a file-scope cell is a borrow of that cell for the
call: the cell stays readable and unchanged while the function runs. A
function that only views a global cell therefore must not store into it,
and the store is refused because its separation obligation against the
active loan of the same cell cannot be proved.

```c filename=viewed_global.c
int32 words[2];
void set_second() { words[1] = 7; }
```

```click
verifying "viewed_global.c";
void set_second() {
    views words[1..2];
    ensures words[1] == 7;
}
```

```expect
fail: unproved obligation: `separate(
```
