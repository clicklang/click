# Scoped introduction proves one goal

A named universal introduction and an implication introduction can nest. In a
function proof, closing the block returns focus to the next claim. Here the
fresh `x` shadows the function parameter only inside the block.

```c filename=scoped_intro.c
int scoped_claim(int x) { return x; }
```

```click
verifying "scoped_intro.c";

theorem scoped_implication() {
    ensures forall (written: Integer) { 1 <= written implies 0 < written } by {
        intro(k) {
            intro() {
                solve() using { 1 <= k; };
            }
        }
    }
}

int32 scoped_claim(int32 x) {
    ensures forall (x: int32) { x == x };
    ensures result == x;
} by {
    step_until(function.exit);
    intro() {
        have result == outer.x by { known(); }
        normalize();
    }
    known();
}
```

```expect
pass
```
