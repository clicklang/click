# An entry pointer may read the scalar it designates

```c filename=probe.c
struct Pair { int32 first; int32 second; };
struct Holder { int32* link; };
int32 probe(struct Holder* holder, struct Pair* pair) {
    return holder->link[0];
}
```

```click
verifying "probe.c";
int32 probe(struct Holder* holder, struct Pair* pair) {
    requires holder->link == &pair->first;
    views holder->link;
    views pair->first;
    views pair->second;
} by { execute(); simp(); }
```

```expect
pass
```
