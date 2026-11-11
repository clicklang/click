# a known fold body fact still accepts an explicit proof

The requirement states the body fact exactly. Folding still generates that obligation; the written proof can close it by assumption.

```c filename=fold_by_proves_an_already_known_body_fact.c
void make(int32 x) { }
```

```click
verifying "fold_by_proves_an_already_known_body_fact.c";
resource positive(n: int32) { fact n > 0; }
void make(int32 x) {
    requires x > 0;
    produces positive(x);
} by {
    fold(positive(x)) by { solve(); }
}
```

```expect
pass
```
