# C file aliases use the filename stem

A file in a subdirectory supplies its stem. Renaming a file with a
duplicate stem lets the other file use the default. The Click list module
keeps its qualifier even when a C file is named `list.c`.

```c filename=left/table.c
static unsigned long count = 7;
```

```c filename=right/table.c
struct state { unsigned long count; };
static struct state suite = {19};
```

```c filename=list.c
static unsigned long other = 3;
```

```c filename=main.c
int main(void) { return 0; }
```

```click
verifying "left/table.c" as left;
verifying "right/table.c";
verifying "list.c";
verifying "main.c";

int32 main() {
    ensures left::count == 7u64;
    ensures table::suite.count == 19u64;
}

theorem list_qualifier() {
    ensures list::length(List<int32>::Nil) == Nat::Zero by {
        unfold(list::length(List<int32>::Nil));
        close();
    }
}
```

```expect
pass
```
