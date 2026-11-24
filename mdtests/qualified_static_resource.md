# A resource can own private storage in multiple files

```c filename=left.c
static unsigned long count = 7;
void clear(void) { count = 0; }
```

```c filename=right.c
static unsigned long count = 19;
unsigned long read_right(void) { return count; }
```

```c filename=main.c
void clear(void);
unsigned long read_right(void);
int main(void) { clear(); return read_right() == 19; }
```

```click
verifying "left.c";
verifying "right.c" as right_file;
verifying "main.c";

resource both() {
    owns left::count;
    owns right_file::count;
    fact right_file::count == 19u64;
}

void clear() {
    owns both();
    ensures left::count == 0u64;
    ensures right_file::count == old(right_file::count);
} by { unfold(both()); step_until(function.exit); fold(both()); close(); }

unsigned long read_right() {
    owns both();
    ensures result == old(right_file::count);
    ensures result == 19u64;
} by { unfold(both()); step_until(function.exit); fold(both()); close(); }

int main() {
    ensures result == 1;
} by { fold(both()); }
```

```expect
pass
```
