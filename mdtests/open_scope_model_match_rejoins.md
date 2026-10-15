# Model matches can rejoin and close before further execution

The interface rejoins both live arms. The table closes at the current program
point and can be borrowed again before executing the return.

```c filename=scope_match.c
int32 read(int32* p) { return 7; }
```

```click
verifying "scope_match.c";
spec enum Pair { First(int32), Second(int32) }
resource cell(p: int32*) {
    field model: Pair;
    match model {
        Pair::First(value) => { owns *p; fact *p == value; },
        Pair::Second(value) => { owns *p; fact *p == value; },
    }
}
resource table(p: int32*) { views *p; fact *p == 7; }
int32 read(int32* p) {
    owns c: cell(p);
    views table(p + 1);
    ensures *(p + 1) == 7;
    ensures result == 7;
} by {
    open(table(p + 1)) {
        match c.model ensuring { owns c: cell(p); } {
            Pair::First(value) => {
                unfold(c);
                let c = fold(cell(p), { model: Pair::First(value) });
            },
            Pair::Second(value) => {
                unfold(c);
                let c = fold(cell(p), { model: Pair::Second(value) });
            },
        }
    }
    open(table(p + 1)) { }
    execute(); simp();
}
```

```expect
pass
```
