# a have refuses auto

`auto` is `execute(); simp();`: it runs the C to function exit. A `have`
proves a fact at the current point and must not advance the program, so
`auto` is refused there and the refusal names `simp`.

```click
theorem have_refuses_auto(x: int32) {
    requires 0 <= x;
    ensures 0 <= x by {
        have x == x by auto;
        assumption();
    }
}
```

```expect
fail: `auto` executes C to function exit, so it cannot prove a `have`; write `have P;` or `have P by simp;`
```
