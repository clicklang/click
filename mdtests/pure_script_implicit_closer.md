# Written proofs of pure goals get an implicit closer

The closer works from the goal left by the written steps, including inside
a local proof.

```c filename=pure_script_implicit_closer.c
int four(int x) { return x + 1; }
```

```click
verifying "pure_script_implicit_closer.c";

function successor(n: int32) -> int32 { n + 1 }

theorem finishes_after_unfold(x: int32) {
    requires x == 3;
    ensures successor(x) == 4 by {
        unfold(successor(x));
    }
}

theorem finishes_a_local_proof(x: int32) {
    requires x == 3;
    ensures successor(x) == 4 by {
        have successor(x) == 4 by {
            unfold(successor(x));
        }
    }
}

theorem finishes_each_conjunct(x: int32, y: int32) {
    requires x == 3;
    requires y == 4;
    ensures successor(x) == 4 and successor(y) == 5 by {
        all {
            successor(x) == 4 => { unfold(successor(x)); }
            successor(y) == 5 => { unfold(successor(y)); }
        }
    }
}

int32 four(int32 x) {
    requires x == 3;
    ensures result == 4;
} by {
    have successor(x) == 4 by {
        unfold(successor(x));
    }
}
```

```expect
pass
```
