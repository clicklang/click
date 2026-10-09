# A folded ordinary composite supports its children's views

Each arm calls a helper that returns `ready_permit(key)`, then folds the
permit into `ready_bundle(key)`. The branch interface keeps the bundle and
views the permit inside it.

A fold consumes the contained children, and the folded head then supports
views of those children. The checked exchange was once kept for every family, so the view was gone and the kernel rejected the
interface. `ready_bundle` is not `authorized` and reaches no population. Its
fold now keeps the ordinary law, which supports the children's views. A
family that reaches a population still keeps only the checked exchange.

```c filename=select_guarded_left.c
int32 select_guarded_left(int32 key) {
    return key;
}
```

```c filename=select_guarded_right.c
int32 select_guarded_right(int32 key) {
    return key;
}
```

```c filename=select_guarded.c
int32 select_guarded(int32 key, int32 choose_left) {
    int32 selected;
    if (choose_left != 0) {
        selected = select_guarded_left(key);
    } else {
        selected = select_guarded_right(key);
    }
    return selected;
}
```

```click
abstract resource left_path(key: int32);
abstract resource right_path(key: int32);
abstract resource ready_permit(key: int32);

resource ready_bundle(key: int32) {
    if key >= 0 {
        owns ready_permit(key);
    }
}

verifying "select_guarded_left.c";
verifying "select_guarded_right.c";
verifying "select_guarded.c";

int32 select_guarded_left(int32 key) {
    consumes left_path(key);
    consumes ready_permit(key);

    produces ready_permit(key) by auto;
    ensures result == key by auto;
}

int32 select_guarded_right(int32 key) {
    consumes right_path(key);
    consumes ready_permit(key);

    produces ready_permit(key) by auto;
    ensures result == key by auto;
}

int32 select_guarded(int32 key, int32 choose_left) {
    requires key >= 0;
    consumes left_path(key);
    consumes right_path(key);
    consumes ready_permit(key);

    ensures result >= 0 by {
        step();
        branch ensuring {
            fact selected == key;
            owns ready_bundle(key);
            views ready_permit(key);
        } then {
            step();
            fold(ready_bundle(key));
        } else {
            step();
            fold(ready_bundle(key));
        }
        step();
        simp();
    }
}
```

```expect
pass
```
