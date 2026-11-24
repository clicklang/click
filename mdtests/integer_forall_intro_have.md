# Integer intro carries the focused binding into a nested have

```click
theorem integer_forall_intro_have() {
    ensures forall (z: Integer) { z == z } by {
        intro();
        have z == z by close();
        close();
    }
}
```

```expect
pass
```
