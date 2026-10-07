# An ordinary composite of tokens folds by its definition in authority mode

The composite and the resources it holds are declared without `authorized`,
so the composite reaches no population. In an authority-mode project it folds
and unfolds by its definition rather than as a population transfer wrapper.

```c filename=use_bundle.c
int32 use_bundle(int32 x) {
    return x;
}
```

```c filename=fold_then_call.c
int32 fold_then_call(int32 x) {
    int32 value;
    value = use_bundle(x);
    return value;
}
```

```click resource_semantics=authority
abstract resource permit(x: int32);

resource bundle(x: int32) {
    contains permit(x);
    fact x >= 0;
}

verifying "use_bundle.c";
verifying "fold_then_call.c";

int32 use_bundle(int32 x) {
    consumes bundle(x);

    produces bundle(x) by auto;
}

int32 fold_then_call(int32 x) {
    consumes bundle(x);

    produces bundle(x) by {
        unfold(bundle(x));
        step();
        fold(bundle(x));
        step();
        step();
    }
}
```

```expect
pass
```
