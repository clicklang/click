# An alias of a complete entry pointer read retains its scalar extent

```c filename=probe.c
struct Pair { int32 first; int32 second; };
struct Holder { int32* link; };
int32 probe(struct Holder* first, struct Holder* alias, struct Pair* pair) {
    return alias->link[1];
}
```

```click
verifying "probe.c";
int32 probe(struct Holder* first, struct Holder* alias, struct Pair* pair) {
    requires first == alias;
    requires first->link == &pair->first;
    views first->link;
    views pair->first;
    views pair->second;
} by { execute(); simp(); }
```

```expect
fail: outside
```
