# `have name: P` names a fact

A `have` may name its fact. Until the end of the enclosing block, the name
stands for the proposition wherever a proposition is cited whole: in
`using { name; }`, `have name by known();`, `contradiction(name)` and the like. The
name is read as `P` where it is cited, so a named fact proves exactly what
restating `P` there proves. It is not visible inside its own proof, and a
nested block or an `if` arm ends its names with the block.

```click
theorem cite_in_using(x: int32) {
    requires x == 5;
    ensures to_integer(x + 1) == 6 by {
        have five: x == 5;
        close() using { five; };
    }
}

theorem named_equalities_support_rewrite(x: int32, y: int32) {
    requires x == 5;
    requires y == x;
    ensures y == 5 by {
        have same: y == x;
        rewrite(y, x);
        have five: x == 5;
        rewrite(x, 5);
        known();
    }
}

theorem cite_in_contradiction(x: int32) {
    requires x == 5;
    requires x != 5;
    ensures false by {
        have five: x == 5;
        contradiction(five);
    }
}

theorem cite_after_its_proof(x: int32) {
    requires x == 5;
    ensures to_integer(x + x) == 10 by {
        have twice: to_integer(x + x) == 10 by {
            close() using { x == 5; };
        }
        close() using { twice; };
    }
}

theorem one_name_in_each_arm(x: int32) {
    requires x == 5;
    ensures x == 5 by {
        if x >= 0 {
            have side: x >= 0;
            close() using { x == 5; };
        } else {
            have side: x < 0;
            close() using { x == 5; };
        }
    }
}
```

```expect
pass
```
