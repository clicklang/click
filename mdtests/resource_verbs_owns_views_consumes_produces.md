# The four resource verbs

`owns` keeps a resource across the call, `views` borrows it read-only,
`consumes` takes it without returning it, and `produces` returns a new one;
`reopen` composes `close` and `open` and ends with the token it started with.

```c filename=resource_verbs.c
extern int32 close(int32 fd);
extern int32 open(int32 fd);

int32 update(int32* p) {
    p[0] = 1;
    return 0;
}

int32 inspect(int32* p) {
    return p[0];
}

int32 reopen(int32 fd) {
    close(fd);
    return open(fd);
}
```

```click
abstract resource open_fd(fd: int32);

verifying "resource_verbs.c";

int32 update(int32* p) {
    owns p[0..1];
}

int32 inspect(int32* p) {
    views p[0..1];
}

extern int32 close(int32 fd) {
    consumes open_fd(fd);
}

extern int32 open(int32 fd) {
    produces open_fd(fd);
}

int32 reopen(int32 fd) {
    owns open_fd(fd) by auto();
}
```

```expect
pass
```
