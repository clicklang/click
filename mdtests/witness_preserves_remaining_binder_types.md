# Witness substitution preserves the remaining binder types

Values match binders in declaration order. An Integer witness can leave an
enum binder open, and an enum witness can leave an Integer binder open.

```click
spec enum Flag { Set }

theorem integer_first() {
    ensures exists (i: Integer, f: Flag) { i == 3 and f == Flag::Set } by {
        witness(3, Flag::Set);
        close();
    }
}

theorem enum_first() {
    ensures exists (f: Flag, i: Integer) { f == Flag::Set and i == 3 } by {
        witness(Flag::Set);
        witness(3);
        close();
    }
}
```

```expect
pass
```
