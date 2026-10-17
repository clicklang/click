# A C++ namespace may share a Click library module's name

`list` is an implicit Click library module, so `list::append` in a Click
reference names its `append`. In a C++ head it is the namespace member the
program declares. A namespace named after a module the file does not import,
such as `bytes`, is accepted there as well; only a Click reference to
`bytes::count` asks for the import. A class member such as `V::length` does
not declare the bare name `length`, so it does not clash with
`import click::list::{length};`. Before, each of these heads was refused.

```cpp filename=ns.cpp function=caller profile=normal_only
namespace list { int append(int x) noexcept { return x; } }
namespace bytes { int count(int x) noexcept { return x; } }
struct V { static int length(int x) noexcept { return x; } };
int caller(int x) noexcept { return V::length(list::append(bytes::count(x))); }
```

```click
verifying "ns.cpp";
import click::list::{length};

extern int list::append(int x) {
    requires 0 <= x and x <= 1000;
    ensures result == x;
}

extern int bytes::count(int x) {
    requires 0 <= x and x <= 1000;
    ensures result == x;
}

extern int V::length(int x) {
    requires 0 <= x and x <= 1000;
    ensures result == x;
}

int caller(int x) {
    requires 0 <= x and x <= 1000;
    ensures result == x;
} by { execute(); simp(); }
```

```expect
pass
```
