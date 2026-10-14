# A retained old array-cell bound supports the following checked call

```c filename=retained.c
int32 child(int32 value) { return value; }
int32 visit(int32* links, int32 index, int32 n) {
    return child(links[index]);
}
```

```click
verifying "retained.c";
int32 child(int32 value) {
    requires 0 <= value;
    ensures result == value;
} by { execute(); simp(); }
int32 visit(int32* links, int32 index, int32 n) {
    owns links[0..n];
    requires 0 <= index;
    requires index < n;
    requires 0 <= links[index];
    ensures result == old(links[index]);
} by {
    have 0 <= old(links[index]) by assumption();
    execute(); simp();
}
```

```expect
pass
```
