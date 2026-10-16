# Proposition connectives, quantifiers, and `old`

Click propositions use the words `and`, `not`, and `implies`, typed `forall`
and `exists` binders, and `old(...)` for the function-entry state.

```c filename=proposition_forms.c
int32 first_matches(int32 p[], int32 n, int32 x) {
    return x;
}
```

```click
verifying "proposition_forms.c";

int32 first_matches(int32 p[], int32 n, int32 x) {
    requires x >= 0;
    requires 1 <= n;
    owns p[0..n];
    requires p[0] == x;
    ensures result == x and not (result != x) by auto();
    ensures result == x implies result >= 0 by auto();
    ensures p[0] == old(p[0]) by auto();
    ensures forall (k: int32) { 0 <= k and k < n implies p[k] == old(p[k]) } by auto();
    ensures exists (k: int32) { 0 <= k and k < n and p[k] == x } by {
        execute();
        witness { k: 0 };
        simp();
    }
}

theorem quantifier_binders(value: int32) {
    ensures forall (x: int32) { x == x } by auto();
    ensures exists (x: int32) { x == value } by {
        witness { x: value };
        simp();
    }
}
```

```expect
pass
```
