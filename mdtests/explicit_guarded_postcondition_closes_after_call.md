# A guarded postcondition becomes usable when its domain is proved

The callee explicitly guards its arithmetic equality. The caller proves its
no-overflow condition from the bounded operands before using the equality.
The selected-premise proof must also retain that explicit guard.

```c filename=guarded_postcondition_closes_after_call.c
struct box {
    int v;
};

int pick(struct box* b) {
    return 0;
}

int caller(struct box* b) {
    int got;
    got = pick(b);
    if (got == 0) {
        return 0;
    }
    return 1;
}

int restricted(struct box* b) {
    int got;
    got = pick(b);
    if (got == 0) {
        return 0;
    }
    return 1;
}
```

```click
resource counted(b: struct box*) {
    field live: int32;
    owns *b;
    fact 0 <= live;
    fact live <= 100;
}

verifying "guarded_postcondition_closes_after_call.c";

int32 pick(struct box* b) {
    owns st: counted(b);
    ensures result == 0 or result == 1;
    ensures defined(old(st.live) + result) implies to_integer(st.live) == to_integer(old(st.live) + result);
} by {
    let { live: n } = unfold(st);
    let st = fold(counted(b), { live: n });
}

int32 caller(struct box* b) {
    owns st: counted(b);
    requires st.live == 1;
    ensures result == 0 implies st.live == 1;
} by {
    step();
    step(pick, { st: st });
}

int32 restricted(struct box* b) {
    owns st: counted(b);
    requires st.live == 1;
    ensures result == 0 implies st.live == 1;
} by {
    step();
    mark m;
    step(pick, { st: st });
    step();
    branch {
        true => {
            have got == 0 by {
                close();
            }
            have at(m, st.live) == 1 by {
                close();
            }
            have st.live == 1 by {
                close() using {
                    defined(at(m, st.live) + got) implies to_integer(st.live) == to_integer(at(m, st.live) + got);
                    got == 0;
                    at(m, st.live) == 1;
                };
            }
            step();
            close();
        }
        false => {}
    }
    step();
    close();
}
```

```expect
pass
```
