# Scoped introduction proves one goal

A named universal introduction and an implication introduction can nest. In a
function proof, closing the block returns focus to the next claim. Here the
fresh `x` shadows the function parameter only inside the block.

For a written range, one block binds the index and introduces both bounds.
Nested ranges take one nested block each, and an implication written in the
body still takes its own block.

```c filename=scoped_intro.c
int scoped_claim(int x) { return x; }
```

```click
verifying "scoped_intro.c";

theorem scoped_implication() {
    ensures forall (written: Integer) { 1 <= written implies 0 < written } by {
        intro(k) {
            intro() {
                close() using { 1 <= k; };
            }
        }
    }
}

theorem scoped_range(lo: int32, hi: int32) {
    ensures (lo..hi).all(|written| { lo <= written and written < hi }) by {
        intro(i) {
            all {
                lo <= i => { close(); }
                i < hi => { close(); }
            }
        }
    }
}

theorem nested_scoped_ranges(end: uint64) {
    ensures (0u64..end).all(|i| {
        (0u64..i).all(|j| { end == end implies j < end })
    }) by {
        intro() {
            intro() {
                intro() {
                    close() using { j < i; i < end; };
                }
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
        have result == outer.x by { close(); }
        normalize();
    }
    close();
}
```

```expect
pass
```
