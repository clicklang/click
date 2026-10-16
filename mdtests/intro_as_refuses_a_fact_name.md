# `intro() as` refuses a fact name

A variable introduced by `intro() as name` cannot take the name of a fact
named by `have name: P` in scope, since a later citation of the name could
then be read two ways.

```click
theorem t(x: int32) {
    requires x == 5;
    ensures forall (k: int32) { x == 5 } by {
        have five: x == 5;
        intro() as five;
        normalize() using { x == 5; }
    }
}
```

```expect
fail: `intro() as five` would hide the fact named `five` by `have five: ...`; choose another name
```
