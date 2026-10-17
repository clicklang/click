# A selectively imported name reads as the library's only in a Click reference

`import click::list::{append, length};` brings the bare names `append` and
`length` to Click calls. A C function the file verifies may share one of them,
and so may a resource binder: the function head names the C function, and
`unfold(length)` opens the binder, not the library's `length`. Before, both
spellings were rewritten to the library declaration before parsing, so the
head named `click::list::append` and the unfold named an unknown predicate.

```c filename=a.c
int append(int x) { return x + 1; }
void user(int *p) { }
```

```click
verifying "a.c";
import click::list::{append, length};

resource marker(p: int32*) {
    field v: int32;
    owns p[0..1];
}

int append(int x) {
    requires 0 <= x and x <= 1000;
    ensures result == x + 1;
} by { execute(); simp(); }

void user(int32* p) {
    consumes length: marker(p);
    produces y: marker(p);
} by {
    unfold(length);
    let y = fold(marker(p), { v: 0 });
    execute();
    simp();
}

theorem appended(xs: List<int32>) {
    ensures append(List<int32>::Nil, xs) == xs by {
        apply(click::list::append_left_identity(xs));
    }
    ensures length(xs) == length(xs) by simp();
}
```

```expect
pass
```
