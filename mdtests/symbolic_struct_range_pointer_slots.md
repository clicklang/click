# Pointer slots keep their own stride
```c filename=slots.c
struct pt { int32 x; int64 y; };
struct pt* first(struct pt **link) { return *link; }
```
```click
verifying "slots.c";
struct pt* first(struct pt** link) {
    views link[0..1];
    ensures result == link[0];
} by { execute(); simp(); }
```
```expect
pass
```
